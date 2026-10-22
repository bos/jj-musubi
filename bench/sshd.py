"""Stands in for sshd on the hub's machine, for ssh.py.

Usage: sshd.py PORT MUSUBI HUB_DIR

For each connection to 127.0.0.1:PORT, runs `MUSUBI hub connect --dir HUB_DIR` with the
connection as its standard input and output, as sshd runs the one command a machine's key
may run there.
"""

import socket
import subprocess
import sys
import threading


def main():
    port, musubi, hub = int(sys.argv[1]), sys.argv[2], sys.argv[3]
    server = socket.create_server(("127.0.0.1", port))
    while True:
        conn, _ = server.accept()
        conn.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        p = subprocess.Popen([musubi, "hub", "connect", "--dir", hub], stdin=conn, stdout=conn)
        conn.close()
        threading.Thread(target=p.wait, daemon=True).start()


main()
