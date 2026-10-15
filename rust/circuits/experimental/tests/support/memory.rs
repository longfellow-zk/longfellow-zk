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

//! Allocation tracking support for isolated, single-threaded benchmark tests.
//! Timing runs leave bench-memory disabled and use the system allocator directly.

use runtime_algebra::mem::{get_current_allocated, get_peak_allocated, reset_peak};

#[cfg(feature = "bench-memory")]
mod allocator {
    use runtime_algebra::mem::{ALLOCATED, PEAK};
    use std::{
        alloc::{GlobalAlloc, Layout, System},
        sync::atomic::Ordering,
    };

    pub struct TrackingAllocator;

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

pub struct Measurement {
    baseline: usize,
}

pub struct HeapPeak {
    pub baseline: usize,
    pub high: usize,
}

impl Measurement {
    pub fn start() -> Self {
        let baseline = get_current_allocated();
        reset_peak();
        Self { baseline }
    }

    pub fn finish(self) -> HeapPeak {
        HeapPeak {
            baseline: self.baseline,
            high: get_peak_allocated(),
        }
    }
}

impl HeapPeak {
    pub fn additional(&self) -> usize {
        self.high.saturating_sub(self.baseline)
    }
}
