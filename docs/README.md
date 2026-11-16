# User guide

Set up and run jj-musubi, check syncing, and recover from problems.

## Start here

The [quick start](../README.md#quick-start) connects your first machines. For an introduction,
see [What jj-musubi makes possible](../README.md#what-jj-musubi-makes-possible) and
[How jj-musubi works](how-it-works.md). [Safety](safety.md) explains what sync
changes and how it is tested.

## Guides

| What you need | Guide |
| --- | --- |
| Connect machines and install services | [Set up a hub and machines](guides/setup.md) |
| Pick up work, run agents, or resolve concurrent changes | [Work across machines](guides/working-across-machines.md) |
| Recover after snapshots pick up accidental files | [Snapshot limits and cleanup](guides/snapshots.md) |
| Check background services and watch every machine | [Monitor syncing](guides/manage.md#check-syncing) |
| Pause syncing, leave, remove copies, or replace a hub | [Manage hives, machines, and hubs](guides/manage.md) |
| Install a new release or deploy a source build | [Upgrade jj-musubi](guides/upgrading.md) |
| Find why work hasn't arrived | [Start with this copy](troubleshooting.md#start-with-this-copy) |

## Reference and troubleshooting

- [Command reference](reference/commands.md)
- [Configuration, files, and logging](reference/configuration.md)
- [Troubleshooting messages](troubleshooting.md)
- [How jj-musubi compares with other approaches](comparison.md)
- [Changelog](../CHANGELOG.md)

For flags, use built-in help:

```sh
musubi --help
musubi <command> --help
```

## Inside jj-musubi

The [contributor docs](internals/README.md) cover the design, proofs and tests.
