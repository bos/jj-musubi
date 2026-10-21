# How hive settings merge

Status: implemented; design.md, "Hive settings", describes it.

## The rule

Each setting carries the time it was written, by the clock of the machine that wrote it.
When machines disagree, the later time wins. Clock skew can make the wrong one win; that
is accepted.

This is not sound, and doesn't try to be. It is simple, and it does what people expect:
"I changed it at 9, you changed it at 8, mine stands."

## Settings and times

A setting is a remote (by name: its URL and push URL together) or a shared config key.
Its time is the modification time of the file holding it (`.git/config`, or jj's repo
config file) when musubi notices the change.

The recorded settings, the `musubi.settings` attribute, carry each setting's value and
time. Wherever settings merge, at a merge operation or when a machine reconciles its own
config with the hive's, each setting takes whichever side has the later time; equal times
go to the machine name that sorts last.

## The loser

A machine whose value is replaced logs it, from the daemon: the old value, the new one, and
which machine wrote it when. Keeping the old value as a comment in the file is left for
later: `git remote remove` deletes a remote's section and any comment in it, and
`git config --comment` needs Git 2.45.

## Joining

A joining machine takes the hive's value of every setting the hive has, and adds its own
others, even one by a name the hive removed: joining is adding a machine, not changing the
hive's mind. So an old clone that still has a remote the hive deliberately removed brings
it back everywhere; remove it again afterwards.

## Upgrading

Settings recorded before writes were timed take their operation's time. Those records were
complete snapshots, so every setting in one, changed or not, takes its time: where two
untimed records were concurrent and no record follows their merge, the later one now wins
outright, which can undo a change the old three-way merge kept. Any write after upgrading
settles it.

A machine's own record of what it last applied has no times either. Its values lose to the
hive's, and one the hive no longer has at all, because the untimed version recorded
removals by leaving them out, is removed here too. Machines must upgrade together: the
protocol version went up, so an old machine can't misread the new records.

## What this replaced

Before, which side won depended on jj's ordering of a merge's parents by when their last
operations ended, so a machine that changed a remote offline and then committed anything
lost its change. The races tests `the_later_change_to_a_remote_wins`,
`the_later_change_wins_reaching_the_hub_last` and
`working_on_after_the_earlier_change_makes_no_difference` check that the later write wins
instead.
