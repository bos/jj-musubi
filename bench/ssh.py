#!/usr/bin/python3 -I
"""Stands in for ssh to the hub's machine: the scripts' $MUSUBI_SSH.

musubi runs `ssh [OPTION...] -- DEST 'musubi hub connect'`. DEST here is 127.0.0.1:PORT, a
route of proxy.py to sshd.py, which runs `musubi hub connect` at the other end; this relays
standard input and output to it. The scripts give each machine its key beforehand, so
musubi never asks this to add one to authorized_keys.
"""

import os
import socket
import sys
import threading


def main():
    args = sys.argv[sys.argv.index("--") + 1 :]
    dest, command = args[0], " ".join(args[1:])
    if command != "musubi hub connect":
        sys.exit(f"ssh.py runs only `musubi hub connect`, not {command!r}")
    host, port = dest.rsplit(":", 1)
    conn = socket.create_connection((host, int(port)))
    conn.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)

    def up():
        try:
            while data := os.read(0, 262144):
                conn.sendall(data)
            conn.shutdown(socket.SHUT_WR)
        except OSError:
            pass

    threading.Thread(target=up, daemon=True).start()
    try:
        while data := conn.recv(262144):
            view = memoryview(data)
            while view:
                view = view[os.write(1, view) :]
    except (BrokenPipeError, ConnectionResetError):
        pass


main()
