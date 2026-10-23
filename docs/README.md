# User guide

musubi keeps a jj repository in sync across your machines. These guides explain how to set it
up, what to expect day to day, and what to do when something goes wrong.

## Start here

- [Quick start](../README.md#quick-start)
- [How musubi works](how-it-works.md)

## Guides

- [Set up a hub and machines](guides/set-up.md)
- [Work across machines](guides/working-across-machines.md)
- [Manage hives, machines, and hubs](guides/manage.md)

## Reference and troubleshooting

- [Command reference](reference/commands.md)
- [Configuration, files, and logging](reference/configuration.md)
- [Troubleshooting](troubleshooting.md)
- [How musubi compares with other approaches](comparison.md)
- [Changelog](../CHANGELOG.md)

For every flag, use the built-in help:

```sh
musubi --help
musubi <command> --help
```

## Inside musubi

The [contributor docs](internals/README.md) cover the design, the sync protocol and its Lean
proofs, every race between machines that musubi tests, and how it is tested.
