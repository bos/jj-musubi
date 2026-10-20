"""Byte-counting TCP proxy, with optional added latency.

Usage: proxy.py CONTROL_PORT NAME:LISTEN_PORT:TARGET_PORT[:ONE_WAY_DELAY_MS] [...]

Each route forwards 127.0.0.1:LISTEN_PORT to 127.0.0.1:TARGET_PORT and counts payload bytes
in both directions (up = client to server, down = server to client), plus connections.
With a delay, every byte is held for ONE_WAY_DELAY_MS in each direction (so the round trip
grows by twice that), with unlimited buffering: a pure-latency link with no bandwidth cap.
Connecting to CONTROL_PORT and sending "GET\n" returns the counters as one JSON line.
Counts are of TCP payload (application bytes), not IP/TCP headers.
"""

import asyncio
import json
import socket
import sys

counters = {}


async def pump(reader, writer, route, key, delay):
    loop = asyncio.get_running_loop()
    queue = asyncio.Queue()

    async def read_side():
        try:
            while True:
                data = await reader.read(262144)
                queue.put_nowait((loop.time() + delay, data))
                if not data:
                    break
        except (ConnectionResetError, BrokenPipeError):
            queue.put_nowait((loop.time() + delay, b""))

    async def write_side():
        try:
            while True:
                due, data = await queue.get()
                now = loop.time()
                if due > now:
                    await asyncio.sleep(due - now)
                if not data:
                    break
                counters[route][key] += len(data)
                writer.write(data)
                await writer.drain()
        except (ConnectionResetError, BrokenPipeError):
            pass
        finally:
            try:
                writer.close()
            except Exception:
                pass

    await asyncio.gather(read_side(), write_side())


def make_handler(route, target, delay):
    async def handle(client_reader, client_writer):
        counters[route]["conns"] += 1
        try:
            server_reader, server_writer = await asyncio.open_connection("127.0.0.1", target)
        except OSError:
            client_writer.close()
            return
        for w in (client_writer, server_writer):
            sock = w.get_extra_info("socket")
            if sock is not None:
                sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        await asyncio.gather(
            pump(client_reader, server_writer, route, "up", delay),
            pump(server_reader, client_writer, route, "down", delay),
        )

    return handle


async def control(reader, writer):
    line = await reader.readline()
    if line.strip() == b"GET":
        writer.write((json.dumps(counters) + "\n").encode())
    await writer.drain()
    writer.close()


async def main():
    control_port = int(sys.argv[1])
    servers = []
    for spec in sys.argv[2:]:
        parts = spec.split(":")
        name, listen, target = parts[0], int(parts[1]), int(parts[2])
        delay = float(parts[3]) / 1000 if len(parts) > 3 else 0.0
        counters[name] = {"up": 0, "down": 0, "conns": 0}
        servers.append(
            await asyncio.start_server(make_handler(name, target, delay), "127.0.0.1", listen)
        )
    servers.append(await asyncio.start_server(control, "127.0.0.1", control_port))
    print("ready", flush=True)
    await asyncio.gather(*(s.serve_forever() for s in servers))


asyncio.run(main())
