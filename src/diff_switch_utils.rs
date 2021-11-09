use crate::bitset::BitSet32;

/// An aggregator type used to help identify the union of explicit difficulty levels
/// between all of the difficulty switches in a statement.
///
/// For instance, if an expression contains two switches that look like `(a:b)` and `(a:::d:)`,
/// then difficulties 0, 1, and 3 are all explicit, and the maximum length is 5.
pub struct MaximalSwitchProps {
    pub maximal_len: usize,
    /// indices where at least one switch had a value
    pub explicit_difficulties: BitSet32,
}

impl MaximalSwitchProps {
    pub fn new() -> Self { MaximalSwitchProps {
        maximal_len: 1,
        explicit_difficulties: BitSet32::from_mask(1),
    }}

    pub fn update<T>(&mut self, switch_cases: &[Option<T>]) {
        self.maximal_len = self.maximal_len.max(switch_cases.len());

        for (difficulty, case) in switch_cases.iter().enumerate() {
            if case.is_some() {
                self.explicit_difficulties.insert(difficulty as u32);
            }
        }
    }
}

/// Grab the corresponding item from difficulty cases.
/// (the final value is assumed to repeat forever)
pub fn select_diff_switch_case<T>(cases: &[Option<T>], difficulty: u32) -> &T {
    let start = usize::min(cases.len() - 1, difficulty as usize);
    (0..=start).rev()  // start from difficulty and look backwards
        .filter_map(move |i| cases[i].as_ref()).next()  // find first Some
        .expect("there's always an easy value")
}

pub fn explicit_difficulty_cases<T>(cases: &[Option<T>]) -> Vec<(BitSet32, &T)> {
    let mut remaining = cases.iter();
    let mut cur_case = remaining.next().expect("always len > 1").as_ref().expect("first case always present");
    let mut cur_mask = BitSet32::from_bit(0);
    let mut difficulty = 1;
    let mut out = vec![];
    for case_opt in remaining {
        if let Some(case) = case_opt {
            out.push((cur_mask, cur_case));
            cur_case = case;
            cur_mask = BitSet32::new();
        }
        cur_mask.insert(difficulty);
        difficulty += 1;
    }
    out.push((cur_mask, cur_case));
    out
}

/// Get masks for each difficulty case based on how it is repeated.
/// The input list of indices must be sorted.
///
/// For instance, a switch like `(a:::b:)` will produce two masks, `0b111` (for `a`) and `0b11000` (for `b`).
pub fn explicit_case_bitmasks(explicit_difficulties: impl IntoIterator<Item=u32>, len: usize) -> impl Iterator<Item=BitSet32> {
    let mut stops = explicit_difficulties.into_iter().chain(core::iter::once(len as u32));

    let mut prev = stops.next().expect("always at least one case");
    stops.map(move |stop| {
        debug_assert!(prev < stop, "explicit_difficulties not sorted, or bad len");
        let bitset = (prev..stop).collect();
        prev = stop;
        bitset
    })
}

#[test]
fn test_difficulty_cases() {
    let m = BitSet32::from_mask;
    assert_eq!(
        explicit_difficulty_cases(&[Some(10), Some(20), Some(30)]),
        vec![(m(1), &10), (m(2), &20), (m(4), &30)],
    );
    assert_eq!(
        explicit_difficulty_cases(&[Some(10), None, None, Some(30), None]),
        vec![(m(0b111), &10), (m(0b11000), &30)],
    );
}

#[test]
fn test_explicit_case_bitmasks() {
    let m = BitSet32::from_mask;
    assert_eq!(
        explicit_case_bitmasks(vec![0, 1, 2], 3).collect::<Vec<_>>(),
        vec![m(1), m(2), m(4)],
    );
    assert_eq!(
        explicit_case_bitmasks(vec![0, 3], 5).collect::<Vec<_>>(),
        vec![m(0b111), m(0b11000)],
    );
}
