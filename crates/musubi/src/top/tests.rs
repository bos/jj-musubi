//! Render and drive the production app without a terminal, network, or wall-clock waits.

use musubi_hub::activity::Accepted;
use musubi_hub::activity::HiveActivity;
use musubi_hub::activity::HubActivity;
use musubi_hub::activity::MachineActivity;
use musubi_hub::activity::Report;
use musubi_hub::activity::Traffic;
use musubi_hub::hub_dir::HiveInfo;
use ratatui::Terminal;
use ratatui::backend::TestBackend;
use ratatui::style::Color;
use ratatui::style::Modifier;
use tokio::time::Instant;

use super::sample::HubSample;
use super::*;

fn hive(name: &str) -> HiveActivity {
    HiveActivity {
        info: HiveInfo {
            id: name.to_owned(),
            name: name.to_owned(),
            backend: musubi_jj::objects::Backend::Git,
            clone_config: Default::default(),
            urls: vec![],
            machines: vec![],
        },
        head: Some(10),
        traffic: Traffic {
            received: 1024,
            sent: 2048,
            ops_in: 2,
            commits_in: 1,
            accepted: 1,
            ..Traffic::default()
        },
        failure: None,
        machines: vec![MachineActivity {
            key: "laptop#1234".to_owned(),
            name: "laptop".to_owned(),
            in_view: true,
            heard: Some(1),
            report: Some(Report {
                machine: "laptop#1234".to_owned(),
                seq: 10,
                error: None,
                version: "0.5.0".to_owned(),
            }),
            behind: None,
        }],
        recent: vec![Accepted {
            age: 2,
            seq: 10,
            ops: 2,
            commits: 1,
            host: "laptop".to_owned(),
            description: format!("commit in {name}"),
        }],
    }
}

fn sample() -> Sample {
    Sample {
        hubs: vec![HubSample {
            hub: "devbox".to_owned(),
            at: Instant::now(),
            activity: Ok(HubActivity {
                version: "0.5.0".to_owned(),
                uptime: 120,
                hives: vec![hive("app"), hive("guide")],
            }),
        }],
        daemon: Ok(Some(2)),
        copies: true,
    }
}

fn key(app: &mut App, code: KeyCode) -> Action {
    app.key(KeyEvent::new(code, KeyModifiers::NONE))
}

fn draw(app: &mut App, width: u16, height: u16) -> Terminal<TestBackend> {
    let mut terminal = Terminal::new(TestBackend::new(width, height)).unwrap();
    terminal.draw(|frame| app.draw(frame)).unwrap();
    terminal
}

#[test]
fn loading_and_empty_screens() {
    let mut app = App::new(Duration::from_secs(5));
    insta::assert_snapshot!(draw(&mut app, 40, 4).backend(), @r#"
    "Asking the hubs…                        "
    "                                        "
    "                                        "
    "                                        "
    "#);
    let mut empty = sample();
    empty.hubs[0].activity.as_mut().unwrap().hives.clear();
    app.receive(empty);
    insta::assert_snapshot!(draw(&mut app, 64, 8).backend(), @r#"
    "musubi top: 1 hub, every 5s                                     "
    "This machine's daemon is running, serving 2 repositories.       "
    "Hub devbox: up 2m, musubi 0.5.0, 0 hives.                       "
    "H HEAD   IN/s       OUT/s      OPS     COMMITS  MACHINES  ISSUES"
    "                                                                "
    "                                                                "
    "                                                                "
    "q quit   ↑↓ choose a hive   r refresh   + slower   - faster     "
    "#);
    let mut failed = sample();
    failed.hubs[0].activity = Err("connection refused".to_owned());
    failed.daemon = Err("permission\ndenied".to_owned());
    app.receive(failed);
    insta::assert_snapshot!(draw(&mut app, 64, 10).backend(), @r#"
    "musubi top: 1 hub, every 5s                                     "
    "Issues:                                                         "
    "  This machine's daemon: permission denied                      "
    "  Hub devbox: connection refused                                "
    "H HEAD   IN/s       OUT/s      OPS     COMMITS  MACHINES  ISSUES"
    "                                                                "
    "                                                                "
    "                                                                "
    "                                                                "
    "q quit   ↑↓ choose a hive   r refresh   + slower   - faster     "
    "#);
}

/// Keys change the selected hive and its detail together, including after resize and when
/// a refresh removes the selected row. Snapshots preserve rows; cells pin the highlight.
#[test]
fn navigation_selects_details_and_resize_preserves_selection() {
    let mut app = App::new(Duration::from_secs(5));
    app.receive(sample());
    let mut terminal = draw(&mut app, 80, 24);
    insta::assert_snapshot!(terminal.backend(), @r#"
    "musubi top: 1 hub, every 5s                                                     "
    "This machine's daemon is running, serving 2 repositories.                       "
    "Hub devbox: up 2m, musubi 0.5.0, 2 hives.                                       "
    "HIVE              HEAD   IN/s       OUT/s      OPS     COMMITS  MACHINES  ISSUES"
    "app               #10    —          —          2       1        1/1             "
    "guide             #10    —          —          2       1        1/1             "
    "                                                                                "
    "app since the hub started:                                                      "
    "  received 1.0 KiB and sent 2.0 KiB                                             "
    "  2 operations came in, with 1 commit, and 0 went out                           "
    "  1 push moved the head, and 0 found it moved already                           "
    "MACHINE          HEARD     AT      MUSUBI   STATE                               "
    "laptop           1s ago    #10     0.5.0    up to date                          "
    "                                                                                "
    "AGO       HEAD    FROM             OPS   COMMITS  WHAT                          "
    "2s ago    #10     laptop           2     1        commit in app                 "
    "                                                                                "
    "                                                                                "
    "                                                                                "
    "                                                                                "
    "                                                                                "
    "                                                                                "
    "                                                                                "
    "q quit   ↑↓ choose a hive   r refresh   + slower   - faster                     "
    "#);
    assert_eq!(key(&mut app, KeyCode::Down), Action::None);
    terminal.draw(|frame| app.draw(frame)).unwrap();
    insta::assert_snapshot!(terminal.backend(), @r#"
    "musubi top: 1 hub, every 5s                                                     "
    "This machine's daemon is running, serving 2 repositories.                       "
    "Hub devbox: up 2m, musubi 0.5.0, 2 hives.                                       "
    "HIVE              HEAD   IN/s       OUT/s      OPS     COMMITS  MACHINES  ISSUES"
    "app               #10    —          —          2       1        1/1             "
    "guide             #10    —          —          2       1        1/1             "
    "                                                                                "
    "guide since the hub started:                                                    "
    "  received 1.0 KiB and sent 2.0 KiB                                             "
    "  2 operations came in, with 1 commit, and 0 went out                           "
    "  1 push moved the head, and 0 found it moved already                           "
    "MACHINE          HEARD     AT      MUSUBI   STATE                               "
    "laptop           1s ago    #10     0.5.0    up to date                          "
    "                                                                                "
    "AGO       HEAD    FROM             OPS   COMMITS  WHAT                          "
    "2s ago    #10     laptop           2     1        commit in guide               "
    "                                                                                "
    "                                                                                "
    "                                                                                "
    "                                                                                "
    "                                                                                "
    "                                                                                "
    "                                                                                "
    "q quit   ↑↓ choose a hive   r refresh   + slower   - faster                     "
    "#);
    let buffer = terminal.backend().buffer();
    assert!(buffer[(0, 5)].modifier.contains(Modifier::REVERSED));
    assert!(!buffer[(0, 4)].modifier.contains(Modifier::REVERSED));
    terminal.backend_mut().resize(32, 18);
    terminal.draw(|frame| app.draw(frame)).unwrap();
    insta::assert_snapshot!(terminal.backend(), @r#"
    "musubi top: 1 hub, every 5s     "
    "This machine's daemon is running"
    "Hub devbox: up 2m, musubi 0.5.0,"
    " HEAD IN/ OUT/ OPS COMM MAC ISSU"
    " #10  —   —    2   1    1/1     "
    " #10  —   —    2   1    1/1     "
    "                                "
    "guide since the hub started:    "
    "  received 1.0 KiB and sent 2.0 "
    "KiB                             "
    "  2 operations came in, with 1  "
    "commit, and 0 went out          "
    "  1 push moved the head, and 0  "
    "found it moved already          "
    "MACHINE HEARD   AT      MUSUBI  "
    "laptop  1s ago  #10     0.5.0   "
    "                                "
    "q quit   ↑↓ choose a hive   r re"
    "#);
    assert_eq!(app.selected.selected(), Some(1));
    assert_eq!(key(&mut app, KeyCode::Char('k')), Action::None);
    draw(&mut app, 80, 24);
    assert_eq!(app.selected.selected(), Some(0));
    key(&mut app, KeyCode::Char('j'));
    draw(&mut app, 80, 24);
    assert_eq!(app.selected.selected(), Some(1));
    let mut fewer = sample();
    fewer.hubs[0].activity.as_mut().unwrap().hives.pop();
    app.receive(fewer);
    terminal.backend_mut().resize(80, 24);
    terminal.draw(|frame| app.draw(frame)).unwrap();
    let screen = terminal.backend().to_string();
    assert_eq!(app.selected.selected(), Some(0));
    assert!(screen.contains("app since the hub started:"), "{screen}");
    assert!(!screen.contains("guide"), "{screen}");
    key(&mut app, KeyCode::Up);
    draw(&mut app, 80, 24);
    assert_eq!(app.selected.selected(), Some(0));
}

#[test]
fn unreachable_hubs_and_excess_issues_are_visible_and_red() {
    let mut troubled = sample();
    let hives = &mut troubled.hubs[0].activity.as_mut().unwrap().hives;
    hives[0].machines[0].report.as_mut().unwrap().error = Some("permission denied".to_owned());
    for n in 0..10 {
        troubled.hubs.push(HubSample {
            hub: format!("remote-{n}"),
            at: Instant::now(),
            activity: Err("connection refused".to_owned()),
        });
    }
    let mut app = App::new(Duration::from_secs(5));
    app.receive(troubled);
    let terminal = draw(&mut app, 80, 24);
    insta::assert_snapshot!(terminal.backend(), @r#"
    "musubi top: 11 hubs, every 5s                                                   "
    "This machine's daemon is running, serving 2 repositories.                       "
    "Hub devbox: up 2m, musubi 0.5.0, 2 hives.                                       "
    "Issues:                                                                         "
    "  app: laptop sync failing: permission denied                                   "
    "  Hub remote-0: connection refused                                              "
    "  Hub remote-1: connection refused                                              "
    "  Hub remote-2: connection refused                                              "
    "  Hub remote-3: connection refused                                              "
    "  Hub remote-4: connection refused                                              "
    "  Hub remote-5: connection refused                                              "
    "  and 4 more                                                                    "
    "HIVE     HUB      HEAD   IN/s       OUT/s      OPS     COMMITS  MACHINES  ISSUES"
    "app      devbox   #10    —          —          2       1        0/1       1     "
    "guide    devbox   #10    —          —          2       1        1/1             "
    "                                                                                "
    "app since the hub started:                                                      "
    "  received 1.0 KiB and sent 2.0 KiB                                             "
    "  2 operations came in, with 1 commit, and 0 went out                           "
    "  1 push moved the head, and 0 found it moved already                           "
    "MACHINE          HEARD     AT      MUSUBI   STATE                               "
    "laptop           1s ago    #10     0.5.0    sync failing: permission denied     "
    "                                                                                "
    "q quit   ↑↓ choose a hive   r refresh   + slower   - faster                     "
    "#);
    let buffer = terminal.backend().buffer();
    // Heading, diagnostic, and selected hive row all keep the warning color.
    for y in [3, 4, 13] {
        assert_eq!(buffer[(0, y)].fg, Color::Red);
    }
    // A tiny terminal is reachable by resizing, including to no drawable cells.
    for (width, height) in [(1, 1), (20, 3), (0, 0)] {
        draw(&mut app, width, height);
    }
}

#[test]
fn refresh_speed_and_quit_keys() {
    let mut app = App::new(FASTEST);
    assert_eq!(key(&mut app, KeyCode::Char('r')), Action::Wake(Wake::Now));
    assert_eq!(
        key(&mut app, KeyCode::Char('-')),
        Action::Wake(Wake::Every(FASTEST))
    );
    assert_eq!(
        key(&mut app, KeyCode::Char('+')),
        Action::Wake(Wake::Every(FASTEST * 2))
    );
    app.interval = SLOWEST;
    assert_eq!(
        key(&mut app, KeyCode::Char('+')),
        Action::Wake(Wake::Every(SLOWEST))
    );
    assert_eq!(
        key(&mut app, KeyCode::Char('-')),
        Action::Wake(Wake::Every(SLOWEST - FASTEST))
    );
    for kind in [KeyEventKind::Release, KeyEventKind::Repeat] {
        for code in [KeyCode::Char('q'), KeyCode::Char('+'), KeyCode::Down] {
            assert_eq!(
                app.key(KeyEvent::new_with_kind(code, KeyModifiers::NONE, kind)),
                Action::None
            );
        }
    }
    assert_eq!(app.interval, SLOWEST - FASTEST);
    assert_eq!(app.selected.selected(), Some(0));
    assert_eq!(key(&mut app, KeyCode::Char('c')), Action::None);
    assert_eq!(key(&mut app, KeyCode::Char('?')), Action::None);
    for code in [KeyCode::Char('q'), KeyCode::Esc] {
        assert_eq!(key(&mut app, code), Action::Quit);
    }
    assert_eq!(
        app.key(KeyEvent::new(KeyCode::Char('c'), KeyModifiers::CONTROL)),
        Action::Quit
    );
}

/// Poll the actual sampling loop with Tokio's clock frozen. Each explicit poll runs until
/// it waits again, avoiding scheduling races and Tokio's automatic time advancement.
#[tokio::test(start_paused = true)]
async fn refresh_deadlines_manual_refresh_and_interval_changes() {
    let (send, received) = mpsc::channel();
    let (wake, woken) = tokio::sync::mpsc::unbounded_channel();
    let interval = Duration::from_secs(5);
    let sampling = sample_until_told(async || sample(), interval, send, woken);
    tokio::pin!(sampling);
    assert!(futures::poll!(&mut sampling).is_pending());
    let first = received.try_recv().unwrap();
    let first_at = first.hubs[0].at;
    tokio::time::advance(interval - Duration::from_millis(1)).await;
    assert!(futures::poll!(&mut sampling).is_pending());
    assert!(received.try_recv().is_err());
    tokio::time::advance(Duration::from_millis(1)).await;
    assert!(futures::poll!(&mut sampling).is_pending());
    assert_eq!(received.try_recv().unwrap().hubs[0].at - first_at, interval);

    let mut app = App::new(interval);
    app.receive(first);
    tokio::time::advance(Duration::from_secs(2)).await;
    for code in [KeyCode::Char('r'), KeyCode::Char('+')] {
        let Action::Wake(message) = key(&mut app, code) else {
            panic!("expected refresh")
        };
        wake.send(message).unwrap();
        assert!(futures::poll!(&mut sampling).is_pending());
        app.receive(received.try_recv().unwrap());
        assert_eq!(
            app.latest.as_ref().unwrap().hubs[0].at,
            first_at + interval + Duration::from_secs(2)
        );
    }
    assert_eq!(app.interval, Duration::from_secs(6));
    tokio::time::advance(Duration::from_secs(5)).await;
    assert!(futures::poll!(&mut sampling).is_pending());
    assert!(received.try_recv().is_err());
    tokio::time::advance(Duration::from_secs(1)).await;
    assert!(futures::poll!(&mut sampling).is_pending());
    app.receive(received.try_recv().unwrap());
    assert_eq!(
        app.latest.as_ref().unwrap().hubs[0].at - app.previous.as_ref().unwrap().hubs[0].at,
        app.interval
    );
    drop(wake);
    assert!(futures::poll!(&mut sampling).is_ready());
}

#[tokio::test(start_paused = true)]
async fn a_slow_sample_does_not_block_keys_or_cause_catch_up_refreshes() {
    let (send, received) = mpsc::channel();
    let (wake, woken) = tokio::sync::mpsc::unbounded_channel();
    let (release, mut blocked) = tokio::sync::mpsc::unbounded_channel();
    let sampling = sample_until_told(
        async || {
            blocked.recv().await.unwrap();
            sample()
        },
        Duration::from_secs(5),
        send,
        woken,
    );
    tokio::pin!(sampling);
    assert!(futures::poll!(&mut sampling).is_pending());
    let mut app = App::new(Duration::from_secs(5));
    assert_eq!(key(&mut app, KeyCode::Char('q')), Action::Quit);
    tokio::time::advance(Duration::from_secs(60)).await;
    assert!(futures::poll!(&mut sampling).is_pending());
    assert!(received.try_recv().is_err());
    release.send(()).unwrap();
    release.send(()).unwrap();
    assert!(futures::poll!(&mut sampling).is_pending());
    let first = received.try_recv().unwrap();
    assert!(received.try_recv().is_err());
    tokio::time::advance(Duration::from_secs(5)).await;
    assert!(futures::poll!(&mut sampling).is_pending());
    assert_eq!(
        received.try_recv().unwrap().hubs[0].at - first.hubs[0].at,
        Duration::from_secs(5)
    );
    // Closing the screen's receiver also ends sampling, even if the wake sender lives on.
    drop(received);
    release.send(()).unwrap();
    wake.send(Wake::Now).unwrap();
    assert!(futures::poll!(&mut sampling).is_ready());
}

#[tokio::test(start_paused = true)]
async fn rates_follow_virtual_time_and_reset_after_a_hub_restart() {
    let mut app = App::new(Duration::from_secs(5));
    app.receive(sample());
    tokio::time::advance(Duration::from_secs(2)).await;
    let mut next = sample();
    let activity = next.hubs[0].activity.as_mut().unwrap();
    activity.uptime += 2;
    activity.hives[0].traffic.received += 4096;
    app.receive(next);
    let screen = draw(&mut app, 80, 24).backend().to_string();
    assert!(screen.contains("2.0 KiB/s"), "{screen}");
    // Refreshes at the same instant have no rate, not infinity or a divide by zero.
    let mut simultaneous = sample();
    simultaneous.hubs[0].activity.as_mut().unwrap().uptime = 122;
    app.receive(simultaneous);
    let screen = draw(&mut app, 80, 24).backend().to_string();
    assert!(
        screen.contains("app               #10    —          —"),
        "{screen}"
    );
    tokio::time::advance(Duration::from_secs(2)).await;
    let mut restarted = sample();
    restarted.hubs[0].activity.as_mut().unwrap().uptime = 1;
    app.receive(restarted);
    let screen = draw(&mut app, 80, 24).backend().to_string();
    assert!(
        screen.contains("app               #10    —          —"),
        "{screen}"
    );
}
