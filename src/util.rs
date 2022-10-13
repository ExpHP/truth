use indexmap::IndexMap;

pub fn get_groups_by<T, K: Eq + core::hash::Hash>(
    items: impl Iterator<Item=T>,
    mut key_fn: impl FnMut(&T) -> K,
) -> IndexMap<K, Vec<T>> {
    let mut out = IndexMap::<_, Vec<_>>::default();
    for item in items {
        out.entry(key_fn(&item)).or_default().push(item);
    }
    out
}
