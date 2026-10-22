//! Whether the machine runs on battery, when musubi defers its gc. A `pre-auto-gc` hook,
//! such as the `pre-auto-gc-battery` that git used to ship, could defer it before musubi
//! stopped running hooks.

use std::path::Path;

/// Whether the machine runs on battery; false where that can't be told.
#[cfg(target_os = "macos")]
pub fn on_battery() -> bool {
    std::process::Command::new("/usr/bin/pmset")
        .args(["-g", "batt"])
        .output()
        .is_ok_and(|output| drawing_from_battery(&String::from_utf8_lossy(&output.stdout)))
}

/// Whether the machine runs on battery; false where that can't be told.
#[cfg(target_os = "linux")]
pub fn on_battery() -> bool {
    discharging(Path::new("/sys/class/power_supply"))
}

/// Whether the machine runs on battery; false where that can't be told.
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub fn on_battery() -> bool {
    false
}

/// Whether `pmset -g batt` says the machine draws from something other than AC, on its
/// first line: "Now drawing from 'Battery Power'", or a UPS.
#[cfg_attr(
    not(target_os = "macos"),
    allow(dead_code, reason = "macOS, and tests")
)]
fn drawing_from_battery(pmset: &str) -> bool {
    pmset
        .lines()
        .next()
        .is_some_and(|line| line.starts_with("Now drawing from") && !line.contains("'AC Power'"))
}

/// Whether the machine runs on battery, by sysfs's `power_supply` (`/sys/class/...`): when
/// no mains or USB supply is online and one of the machine's own batteries is discharging.
/// Some laptops say their battery is discharging on AC, at a charge threshold, say; and a
/// wireless mouse's or keyboard's battery is there too, with `scope` `Device`, and says
/// nothing about the machine.
#[cfg_attr(
    not(target_os = "linux"),
    allow(dead_code, reason = "Linux, and tests")
)]
fn discharging(power_supply: &Path) -> bool {
    let Ok(supplies) = std::fs::read_dir(power_supply) else {
        return false;
    };
    let mut discharging = false;
    for supply in supplies.flatten() {
        let read = |name: &str| {
            let text = std::fs::read_to_string(supply.path().join(name)).unwrap_or_default();
            text.trim().to_owned()
        };
        if read("scope") == "Device" {
            continue;
        }
        match read("type").as_str() {
            "Mains" | "USB" if read("online") == "1" => return false,
            "Battery" => discharging |= read("status") == "Discharging",
            _ => {}
        }
    }
    discharging
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn pmset_says_what_the_machine_draws_from() {
        let batt = "\t-InternalBattery-0 (id=23461987)\t100%; charged; 0:00 remaining\n";
        let drawing =
            |from: &str| drawing_from_battery(&format!("Now drawing from {from}\n{batt}"));
        assert!(!drawing("'AC Power'"));
        assert!(drawing("'Battery Power'"));
        assert!(drawing("'UPS Power'"));
        assert!(!drawing_from_battery(""));
    }

    #[test]
    fn only_the_machines_own_battery_off_mains_counts() {
        let dir = tempfile::tempdir().unwrap();
        let supply = |name: &str, files: &[(&str, &str)]| {
            let path = dir.path().join(name);
            fs::create_dir_all(&path).unwrap();
            for (file, contents) in files {
                fs::write(path.join(file), format!("{contents}\n")).unwrap();
            }
        };
        assert!(!discharging(&dir.path().join("missing")));
        supply("AC", &[("type", "Mains"), ("online", "0")]);
        supply("BAT0", &[("type", "Battery"), ("status", "Charging")]);
        supply(
            "hidpp_battery_0",
            &[
                ("type", "Battery"),
                ("scope", "Device"),
                ("status", "Discharging"),
            ],
        );
        assert!(!discharging(dir.path()));
        supply("BAT0", &[("status", "Discharging")]);
        assert!(discharging(dir.path()));
        // Plugged in, though the battery says otherwise.
        supply("AC", &[("online", "1")]);
        assert!(!discharging(dir.path()));
    }
}
