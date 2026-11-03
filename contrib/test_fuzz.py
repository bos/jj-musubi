"""Check worker limits and failure cleanup without building or running Rust targets."""

import asyncio
from collections import Counter
from contextlib import redirect_stderr
import io
import os
from pathlib import Path
import signal
import sys
import tempfile
import unittest
from unittest.mock import patch

import fuzz


class Planning(unittest.TestCase):
    def test_every_target_gets_a_turn_with_a_shared_budget(self):
        targets = ["a", "b", "c"]
        for jobs in (1, 2, 3, 8):
            counts = Counter(fuzz.plan(targets, jobs, False))
            self.assertEqual(set(counts), set(targets))
            self.assertLessEqual(max(counts.values()) - min(counts.values()), 1)
            self.assertEqual(sum(counts.values()), max(jobs, len(targets)))
            self.assertEqual(fuzz.plan(targets, jobs, True), targets)


@unittest.skipUnless(os.name == "posix", "the runner supports Linux and macOS")
class Processes(unittest.IsolatedAsyncioTestCase):
    async def test_cancellation_during_spawn_keeps_the_process_handle(self):
        created = asyncio.Future()
        handoff = asyncio.Event()
        spawn = asyncio.create_subprocess_exec

        async def delayed_handle(*args, **kwargs):
            process = await spawn(*args, **kwargs)
            created.set_result(process)
            await handoff.wait()
            return process

        with patch.object(asyncio, "create_subprocess_exec", delayed_handle):
            task = asyncio.create_task(fuzz.execute(
                [sys.executable, "-c", "import signal; signal.pause()"], os.environ.copy(),
            ))
            process = await asyncio.wait_for(created, 10)
            try:
                task.cancel()
                handoff.set()
                with self.assertRaises(asyncio.CancelledError):
                    await asyncio.wait_for(task, 10)
                self.assertIsNotNone(process.returncode)
            finally:
                if process.returncode is None:
                    os.killpg(process.pid, signal.SIGKILL)
                    await process.wait()

    async def test_cancellation_kills_a_child_after_its_parent_exits(self):
        ready = asyncio.Future()

        async def connected(reader, writer):
            await reader.readline()
            ready.set_result((reader, writer))

        server = await asyncio.start_server(connected, "127.0.0.1", 0)
        port = server.sockets[0].getsockname()[1]
        child = (
            "import signal, socket; signal.signal(signal.SIGTERM, signal.SIG_IGN); "
            f"s = socket.create_connection(('127.0.0.1', {port})); "
            "s.sendall(b'ready\\n'); signal.pause()"
        )
        parent = (
            "import signal, subprocess, sys; "
            "subprocess.Popen([sys.executable, '-c', sys.argv[1]]); signal.pause()"
        )
        async with server:
            task = asyncio.create_task(fuzz.execute(
                [sys.executable, "-c", parent, child], os.environ.copy(),
            ))
            connection = None
            try:
                reader, connection = await asyncio.wait_for(ready, 10)
                task.cancel()
                with self.assertRaises(asyncio.CancelledError):
                    await asyncio.wait_for(task, 10)
                self.assertEqual(await asyncio.wait_for(reader.read(), 10), b"")
            finally:
                if not task.done():
                    task.cancel()
                    await asyncio.gather(task, return_exceptions=True)
                if connection is not None:
                    connection.close()

    async def test_workers_overlap_and_never_exceed_the_budget(self):
        pending = []
        connections = []
        seen = []
        peaks = []

        async def connected(reader, writer):
            connections.append(writer)
            seen.append(await reader.readline())
            pending.append(writer)
            peaks.append(len(pending))
            # Release a batch only once every slot is occupied. The last batch has one.
            if len(pending) == (1 if len(seen) == 5 else 2):
                for connection in pending:
                    connection.write(b"x")
                    await connection.drain()
                    connection.close()
                pending.clear()

        server = await asyncio.start_server(connected, "127.0.0.1", 0)
        port = server.sockets[0].getsockname()[1]
        source = (
            "import socket, sys; "
            "s = socket.create_connection(('127.0.0.1', int(sys.argv[1]))); "
            "s.sendall(b'ready\\n'); assert s.recv(1) == b'x'"
        )
        commands = [("target", [sys.executable, "-c", source, str(port)])] * 5
        with tempfile.TemporaryDirectory() as directory:
            async with server:
                try:
                    await asyncio.wait_for(
                        fuzz.workers(commands, 2, os.environ.copy(), Path(directory)), 10,
                    )
                finally:
                    for connection in connections:
                        connection.close()
            self.assertEqual(len(list(Path(directory).glob("*.log"))), 5)
        self.assertEqual(len(seen), 5)
        self.assertEqual(max(peaks), 2)

    async def test_failure_keeps_output_and_stops_peers_and_their_children(self):
        connections = {}
        peer_pids = []

        async def connected(reader, writer):
            message = (await reader.readline()).decode().split()
            connections[message[0]] = writer
            if message[0] == "peer":
                peer_pids.extend(map(int, message[1:]))
            if len(connections) == 2:
                connections["crash"].write(b"x")
                await connections["crash"].drain()
                for connection in connections.values():
                    connection.close()

        server = await asyncio.start_server(connected, "127.0.0.1", 0)
        port = server.sockets[0].getsockname()[1]
        peer = """
import os, signal, socket, subprocess, sys
child = subprocess.Popen([sys.executable, '-c', 'import signal; signal.pause()'])
def stop(sig, frame):
    child.wait()
    sys.exit(0)
signal.signal(signal.SIGTERM, stop)
s = socket.create_connection(('127.0.0.1', int(sys.argv[1])))
s.sendall(f'peer {os.getpid()} {child.pid}\\n'.encode())
signal.pause()
"""
        crash = """
import socket, sys
s = socket.create_connection(('127.0.0.1', int(sys.argv[1])))
s.sendall(b'crash\\n')
assert s.recv(1) == b'x'
print('failing input saved')
sys.exit(77)
"""
        with tempfile.TemporaryDirectory() as directory:
            logs = Path(directory)
            queued = logs / "queued"
            commands = [
                ("peer", [sys.executable, "-c", peer, str(port)]),
                ("crash", [sys.executable, "-c", crash, str(port)]),
                ("queued", [sys.executable, "-c",
                            "import pathlib, sys; pathlib.Path(sys.argv[1]).touch()",
                            str(queued)]),
            ]
            output = io.StringIO()
            try:
                async with server:
                    try:
                        with redirect_stderr(output), self.assertRaisesRegex(fuzz.Failed, "77"):
                            await asyncio.wait_for(
                                fuzz.workers(commands, 2, os.environ.copy(), logs), 10,
                            )
                    finally:
                        for connection in connections.values():
                            connection.close()
                self.assertIn("failing input saved", output.getvalue())
                self.assertIn("failing input saved", (logs / "crash-1.log").read_text())
                self.assertFalse(queued.exists())
                self.assertEqual(len(peer_pids), 2)
                for pid in peer_pids:
                    with self.assertRaises(ProcessLookupError):
                        os.kill(pid, 0)
            finally:
                for connection in connections.values():
                    connection.close()

    async def test_cancelling_a_run_waits_for_workers_to_stop(self):
        ready = asyncio.Future()

        async def connected(reader, writer):
            ready.set_result(int(await reader.readline()))
            writer.close()

        server = await asyncio.start_server(connected, "127.0.0.1", 0)
        port = server.sockets[0].getsockname()[1]
        source = (
            "import os, signal, socket, sys; "
            "s = socket.create_connection(('127.0.0.1', int(sys.argv[1]))); "
            "s.sendall(f'{os.getpid()}\\n'.encode()); signal.pause()"
        )
        with tempfile.TemporaryDirectory() as directory:
            async with server:
                task = asyncio.create_task(fuzz.workers(
                    [("target", [sys.executable, "-c", source, str(port)])],
                    1, os.environ.copy(), Path(directory),
                ))
                try:
                    pid = await asyncio.wait_for(ready, 10)
                finally:
                    task.cancel()
                    with self.assertRaises(asyncio.CancelledError):
                        await asyncio.wait_for(task, 10)
        with self.assertRaises(ProcessLookupError):
            os.kill(pid, 0)


if __name__ == "__main__":
    unittest.main()
