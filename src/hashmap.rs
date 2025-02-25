use std::{
    borrow::Borrow,
    hash::{BuildHasher, Hash, Hasher},
    mem,
};

pub struct HashMap<K, V, S = std::hash::RandomState, const LOAD_FACTOR: usize = 75> {
    //buckets: Vec<Slot<RawEntry<K, V>>>,
    buckets: Vec<Option<RawEntry<K, V>>>,
    metadata: Vec<Metadata>,
    size: usize,
    hasher: S,
}

#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq)]
struct Metadata(u8);

struct RawEntry<K, V> {
    key: K,
    value: V,
    hash: u64,
}

impl Metadata {
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0 & 0x01 == 0
    }

    #[inline]
    pub fn is_deleted(&self) -> bool {
        self.0 & 0x02 == 1
    }

    #[inline]
    pub fn is_vacant(&self) -> bool {
        self.0 & 0x03 != 0x01
    }

    #[inline]
    pub fn delete(&mut self) {
        self.0 &= 0xfd;
    }

    #[inline]
    pub const fn new() -> Self {
        Metadata(0)
    }
}

impl<K, V> HashMap<K, V>
where
    K: Eq + Hash,
{
    pub fn with_capacity(capacity: usize) -> Self {
        HashMap::with_capacity_and_hasher(capacity, std::hash::RandomState::new())
    }
}

impl<K, V, S: BuildHasher> HashMap<K, V, S>
where
    K: Eq + Hash,
{
    #[inline]
    pub fn with_capacity_and_hasher(capacity: usize, hasher: S) -> Self {
        Self::with_capacity_and_hasher_and_load_factor(capacity, hasher)
    }
}

impl<const LOAD_FACTOR: usize, K, V, S: BuildHasher> HashMap<K, V, S, LOAD_FACTOR>
where
    K: Eq + Hash,
{
    pub fn with_capacity_and_hasher_and_load_factor(capacity: usize, hasher: S) -> Self {
        const { assert!(LOAD_FACTOR <= 100, "LOAD_FACTOR must be less than 100") }
        let capacity = capacity.next_power_of_two();
        let mut buckets = Vec::with_capacity(capacity);
        buckets.resize_with(capacity, || None);
        let metadata = vec![Metadata::new(); capacity];
        Self {
            buckets,
            metadata,
            size: 0,
            hasher,
        }
    }

    #[inline]
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        if self.size as f64 / self.buckets.len() as f64 >= LOAD_FACTOR as f64 / 100.0 {
            self.scaling();
        }

        let hash = make_hash(&self.hasher, &key);
        self.insert_by_hash(key, value, hash)
    }

    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        Q: Borrow<K>,
    {
        let key = key.borrow();
        let len = self.buckets.len();
        let hash = make_hash(&self.hasher, key);
        let mut index = make_index(hash, len);

        for _ in 0..len {
            let metadata = self.metadata[index];
            // 查看 metadata 最低位
            match metadata {
                // 如果 metadata 全为 0，则说明该位置为empty
                m if m.is_empty() => return None,
                // 如果 metadata 只有最低位为 0，则说明该位置为deleted
                m if m.is_deleted() => {}
                // 该位置存在 entry
                _ => match &self.buckets[index] {
                    Some(RawEntry {
                        key: k,
                        value: v,
                        hash: h,
                    }) if *h == hash && k == key => return Some(v),
                    _ => {}
                },
            }
            index = index + 1 & len - 1;
            continue;
        }
        None
    }

    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        Q: Borrow<K>,
    {
        let key = key.borrow();
        let len = self.buckets.len();
        let hash = make_hash(&self.hasher, key);
        let mut index = make_index(hash, len);

        for _ in 0..len {
            let metadata = self.metadata[index];
            // 查看 metadata 最低位
            match metadata {
                // 如果 metadata 全为 0，则说明该位置为empty
                m if m.is_empty() => return None,
                // 如果 metadata 只有最低位为 0，则说明该位置为deleted
                m if m.is_deleted() => {}
                // 该位置存在 entry
                _ => match &self.buckets[index] {
                    Some(RawEntry {
                        key: k,
                        value: _,
                        hash: h,
                    }) if hash == *h && k == key => {
                        let Some(entry) = mem::replace(&mut self.buckets[index], None) else {
                            unreachable!()
                        };
                        self.metadata[index].delete();
                        self.size -= 1;
                        return Some(entry.value);
                    }
                    _ => {}
                },
            }
            index = index + 1 & len - 1;
            continue;
        }
        None
    }

    pub fn capacity(&self) -> usize {
        self.buckets.capacity()
    }

    pub fn len(&self) -> usize {
        self.size
    }

    fn insert_by_hash(&mut self, key: K, value: V, hash: u64) -> Option<V> {
        let len = self.buckets.len();
        let ideal_index = make_index(hash, len);
        let mut next_index = ideal_index;
        let mut key = key;
        let mut value = value;
        let mut hash = hash;
        loop {
            let metadata = Metadata(0b1);
            match self.metadata[next_index] {
                // 最低位为0
                m if m.is_vacant() => {
                    self.buckets[next_index] = Some(RawEntry { hash, key, value });
                    self.metadata[next_index] = metadata;
                    self.size += 1;
                    break None;
                }
                m if m == metadata => match &mut self.buckets[next_index] {
                    Some(RawEntry {
                        key: k,
                        value: v,
                        hash: entry_hash,
                    }) if *entry_hash == hash => {
                        if k == &key {
                            break Some(std::mem::replace(v, value));
                        } else {
                            let entry_ideal_index = make_index(*entry_hash, len);
                            let distance = make_probe_distance(len, ideal_index, next_index);
                            let entry_distance =
                                make_probe_distance(len, entry_ideal_index, next_index);
                            if entry_distance < distance {
                                let old = mem::replace(
                                    self.buckets[next_index].as_mut().unwrap(),
                                    RawEntry { key, value, hash },
                                );
                                key = old.key;
                                value = old.value;
                                hash = old.hash;
                                self.metadata[next_index] = metadata;
                            }
                        }
                    }
                    _ => {}
                },
                _ => {}
            }
            next_index = (next_index + 1) & (len - 1);
            continue;
        }
    }

    fn scaling(&mut self) {
        let new_len = self.buckets.len() * 2;
        let mut new_buckets = Vec::with_capacity(new_len);
        new_buckets.resize_with(new_len, || None);
        self.metadata = vec![Metadata::new(); new_len];
        let buckets = mem::replace(&mut self.buckets, new_buckets);
        for entry in buckets.into_iter().filter_map(|bucket| bucket) {
            self.insert_by_hash(entry.key, entry.value, entry.hash);
        }
    }

    pub fn shrink(&mut self, len: usize) {
        if len < self.size {
            return;
        }
        let mut new_buckets = Vec::with_capacity(len);
        new_buckets.resize_with(len, || None);
        let buckets = mem::replace(&mut self.buckets, new_buckets);
        for entry in buckets.into_iter().filter_map(|bucket| bucket) {
            self.insert_by_hash(entry.key, entry.value, entry.hash);
        }
    }
}

#[inline]
fn make_hash<K: Hash>(hasher: &impl BuildHasher, key: &K) -> u64 {
    let mut hasher = hasher.build_hasher();
    key.hash(&mut hasher);
    hasher.finish()
}

#[inline(always)]
fn make_index(hash: u64, len: usize) -> usize {
    //(hash % len as u64) as usize
    // len为2的幂次方时, 根据a % b == a & (b - 1), 用位运算代替取模运算
    (hash & len as u64 - 1) as usize
}

#[inline]
fn make_probe_distance(len: usize, ideal_index: usize, actual_index: usize) -> usize {
    if actual_index >= ideal_index {
        actual_index - ideal_index
    } else {
        actual_index + (len - ideal_index)
    }
}

impl<K, V> Default for HashMap<K, V>
where
    K: Eq + Hash,
{
    fn default() -> Self {
        HashMap::with_capacity(8)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::{prelude::*, proptest};

    #[test]
    fn test_new_with_capacity() {
        let capacity = 10;
        let map: HashMap<i32, i32> = HashMap::with_capacity(capacity);
        assert_eq!(map.capacity(), capacity.next_power_of_two());
        assert_eq!(map.len(), 0);
    }

    #[test]
    fn test_insert_and_get() {
        let mut map = HashMap::default();
        assert_eq!(map.insert(1, "one"), None);
        assert_eq!(map.get(&1), Some(&"one"));
        assert_eq!(map.insert(2, "two"), None);
        assert_eq!(map.get(&2), Some(&"two"));
    }

    #[test]
    fn test_insert_overwrite() {
        let mut map = HashMap::default();
        assert_eq!(map.insert(1, "one"), None);
        assert_eq!(map.insert(1, "uno"), Some("one"));
        assert_eq!(map.get(&1), Some(&"uno"));
    }

    #[test]
    fn test_remove() {
        let mut map = HashMap::with_capacity(1);
        assert_eq!(map.insert(-231384446, 0), None);
        assert_eq!(map.insert(2, 0), None);
        assert_eq!(map.remove(&-231384446), Some(0));
        assert_eq!(map.get(&1), None);
    }

    #[test]
    fn test_insert_many() {
        let mut map = HashMap::default();
        for i in 0..100 {
            assert_eq!(map.insert(i, i * 2), None);
        }
        for i in 0..100 {
            assert_eq!(map.get(&i), Some(&(i * 2)));
        }
    }

    proptest! {
        #[test]
        fn test_insert_and_get_proptest(key in any::<i32>(), value in any::<i32>()) {
            let mut map = HashMap::default();
            assert_eq!(map.insert(key, value), None);
            assert_eq!(map.get(&key), Some(&value));
        }
    }

    proptest! {
        #[test]
        fn test_insert_overwrite_proptest(key in any::<i32>(), value1 in any::<i32>(), value2 in any::<i32>()) {
            let mut map = HashMap::default();
            assert_eq!(map.insert(key, value1), None);
            assert_eq!(map.insert(key, value2), Some(value1));
            assert_eq!(map.get(&key), Some(&value2));
        }
    }

    proptest! {
        #[test]
        fn test_insert_many_proptest(keys in prop::collection::vec(any::<i32>(), 1..100)) {
            let mut map = HashMap::default();
            for key in &keys {
                assert_eq!(map.insert(*key, key.wrapping_mul(2)), None);
            }
            for key in &keys {
                assert_eq!(map.get(key), Some(&(key.wrapping_mul(2))));
            }
        }
    }

    proptest! {
        #[test]
        fn test_remove_proptest(keys in prop::collection::vec(any::<i32>(), 1..100)) {
            let mut map = HashMap::default();
            for key in &keys {
                assert_eq!(map.insert(*key, *key), None);
            }
            for key in keys.iter().filter(|i| *i % 2 == 0) {
                assert_eq!(map.remove(key), Some(*key));
                assert_eq!(map.get(key), None);
            }
            for key in keys.iter().filter(|i| *i % 2 == 1) {
                assert_eq!(map.get(key), Some(key));
            }
        }
    }
}
