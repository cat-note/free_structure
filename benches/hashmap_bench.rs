// benches/hashmap_bench.rs
use criterion::{Criterion, black_box, criterion_group, criterion_main};
use std::collections::HashMap as StdHashMap;
use std::hash::{Hash, RandomState};

// 导入自定义的HashMap
use free_structure::HashMap as FreeHashMap;
use rand::{Rng, rng};

macro_rules! benchmark {
    ($c:expr, [$($new_map:expr => $name:literal),*]) => {
        let mut group = $c.benchmark_group("seq_insert");
        $(
            group.bench_function($name, |b| {
                let mut map = $new_map;
                let mut i = 0;
                b.iter(|| {
                    map.insert(black_box(i), black_box(i));
                    i += 1;
                })
            });
        )*
        group.finish();

        let mut group = $c.benchmark_group("random_insert");
        $(
            group.bench_function($name, |b| {
                let mut map = $new_map;
                let mut rng = rng();
                b.iter(|| {
                    let key = rng.random::<u32>();
                    map.insert(black_box(key), black_box(key));
                })
            });
        )*
        group.finish();

        let mut group = $c.benchmark_group("get_all_hit");
        $(
            group.bench_function($name, |b| {
                let mut map = $new_map;
                for i in 0..1000 {
                    map.insert(i, i * 2);
                }
                b.iter(|| {
                    for i in 0..1000 {
                        black_box(map.get(black_box(&i)));
                    }
                })
            });
        )*
        group.finish();

        let mut group = $c.benchmark_group("get_50%_hit");
        $(
            group.bench_function($name, |b| {
                let mut map = $new_map;
                for i in (0..1000).step_by(2) {
                    map.insert(i, i);
                }
                b.iter(|| {
                    for i in 0..1000 {
                        black_box(map.get(black_box(&i)));
                    }
                })
            });
        )*
        group.finish();

        let mut group = $c.benchmark_group("high_collision_insert");
        $(
            group.bench_function($name, |b| {
                #[derive(Debug, Clone, Copy, PartialEq, Eq)]
                struct BadHashKey(u64);

                impl Hash for BadHashKey {
                    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
                        state.write_u64(self.0 % 16); // 强制产生大量哈希冲突
                    }
                }

                b.iter(|| {
                    let mut map = $new_map;
                    for i in 0..10_000 {
                        map.insert(black_box(BadHashKey(i)), black_box(i));
                    }
                })
            });
        )*
        group.finish();
    };
}

fn hashmap_benchmarks(c: &mut Criterion) {
    benchmark!(
        c,
        [
            StdHashMap::with_capacity_and_hasher(8, RandomState::default()) => "StdHashMap",
            FreeHashMap::with_capacity_and_hasher(8, RandomState::default()) => "FreeHashMap"
        ]
    );
}

criterion_group!(benches, hashmap_benchmarks);
criterion_main!(benches);
