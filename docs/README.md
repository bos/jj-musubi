# User guide

musubi keeps your jj repositories in sync across machines. These guides explain how to set it
up, what to expect day to day, and what to do when something goes wrong.

## Start here

| What you need | Where to start |
| --- | --- |
| Understand why you'd use this | [Things you can do](../README.md#things-you-can-do), then [How musubi works](how-it-works.md) |
| Decide whether to try it with your work | [Trying musubi safely](safety.md) |
| Connect your first two machines | [Quick start](../README.md#quick-start) or [Step-by-step setup](guides/setup.md) |
| Find out why work hasn't arrived | [Start with this copy](troubleshooting.md#start-with-this-copy) |
| Recover after accidentally adding many files | [Accidental-file recovery](troubleshooting.md#accidentally-added-files-and-sending-stopped) |
| Pause syncing or stop using musubi | [Pause syncing or leave](guides/manage.md#pause-syncing-or-leave) |
| Keep background services healthy | [A healthy baseline](guides/manage.md#a-healthy-baseline), then [Watch every machine](guides/manage.md#watch-every-machine) |

## Guides

- [Set up a hub and machines](guides/setup.md)
- [Work across machines](guides/working-across-machines.md)
- [Snapshot limits and cleanup](guides/working-across-machines.md#when-snapshots-pick-up-too-much)
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
