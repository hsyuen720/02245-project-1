use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::OnceLock;
use std::time::{SystemTime, UNIX_EPOCH};

static COUNTER: AtomicU64 = AtomicU64::new(0);
static RUN_SEED: OnceLock<u64> = OnceLock::new();

fn run_seed() -> u64 {
    *RUN_SEED.get_or_init(|| {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos() as u64
    })
}

/// Returns a process-unique, monotonic fresh id.
/// Example use: `format!("{}#{}", name.ident, next_fresh_id())`
pub fn next_fresh_id() -> String {
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    format!("_g_{:x}_{:08x}", run_seed(), n)
}