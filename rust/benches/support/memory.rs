// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Benchmark-only allocation counters and optional tracking allocator.
//! Timing runs keep `bench-memory` disabled.

use std::sync::atomic::{AtomicUsize, Ordering};

static ALLOCATED: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);

pub(crate) fn reset_peak() {
    let current = ALLOCATED.load(Ordering::SeqCst);
    PEAK.store(current, Ordering::SeqCst);
}

pub(crate) fn get_peak_allocated() -> usize {
    PEAK.load(Ordering::SeqCst)
}

pub(crate) fn get_current_allocated() -> usize {
    ALLOCATED.load(Ordering::SeqCst)
}

#[cfg(feature = "bench-memory")]
mod allocator {
    use std::{
        alloc::{GlobalAlloc, Layout, System},
        sync::atomic::Ordering,
    };

    use super::{ALLOCATED, PEAK};

    pub(super) struct TrackingAllocator;

    unsafe impl GlobalAlloc for TrackingAllocator {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            let ptr = System.alloc(layout);
            if !ptr.is_null() {
                let live = ALLOCATED.fetch_add(layout.size(), Ordering::SeqCst) + layout.size();
                PEAK.fetch_max(live, Ordering::SeqCst);
            }
            ptr
        }

        unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
            System.dealloc(ptr, layout);
            ALLOCATED.fetch_sub(layout.size(), Ordering::SeqCst);
        }
    }
}

#[cfg(feature = "bench-memory")]
#[global_allocator]
static ALLOCATOR: allocator::TrackingAllocator = allocator::TrackingAllocator;
