use crate::bitset::BitSet32;

/// A Vec containing data per case of a diff switch.  Data is only held in the explicitly-provided
/// cases, and the others are `None`.
///
/// If the length is 1, this does not represent a diff switch, but rather a scalar value.
pub type DiffSwitchVec<T> = Vec<Option<T>>;
/// Slice form of DiffSwitchVec.
pub type DiffSwitchSlice<T> = [Option<T>];

/// A wrapper around [`DiffSwitchVec`] which provides helper methods for specifically
/// treating a Vec of length 1 as a scalar value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MaybeDiffSwitch<T> {
    inner: DiffSwitchVec<T>,
}

impl<T> core::ops::Deref for MaybeDiffSwitch<T> {
    type Target = DiffSwitchSlice<T>;

    fn deref(&self) -> &Self::Target { &self.inner }
}

impl<T> core::ops::DerefMut for MaybeDiffSwitch<T> {
    fn deref_mut(&mut self) -> &mut Self::Target { &mut self.inner }
}

impl<T> MaybeDiffSwitch<T> {
    pub fn new_scalar(item: T) -> Self {
        MaybeDiffSwitch { inner: vec![Some(item)] }
    }
    /// Obtain a [`DiffSwitchSlice`], only if this actually is a diff switch.
    pub fn as_diff_switch(&self) -> Option<&DiffSwitchSlice<T>> {
        match self.len() {
            1 => None,
            _ => Some(self),
        }
    }

    pub fn as_scalar(&self) -> Option<&T> {
        match self.len() {
            1 => Some(self.easy_value()),
            _ => None,
        }
    }

    pub fn is_diff_switch(&self) -> bool {
        self.as_diff_switch().is_some()
    }

    pub fn easy_value(&self) -> &T {
        self[0].as_ref().expect("no easy value?!")
    }

    pub fn iter_explicit_values(&self) -> impl Iterator<Item=&T> + '_ {
        self.iter().filter_map(|opt| opt.as_ref())
    }
}

impl<T> FromIterator<Option<T>> for MaybeDiffSwitch<T> {
    fn from_iter<Ts: IntoIterator<Item=Option<T>>>(iter: Ts) -> Self {
        MaybeDiffSwitch { inner: FromIterator::from_iter(iter) }
    }
}

/// An aggregator type used to help identify the union of explicit difficulty levels
/// between all of the difficulty switches in a statement.
///
/// For instance, if an expression contains two switches that look like `(a:b)` and `(a:::d:)`,
/// then difficulties 0, 1, and 3 are all explicit, and the maximum length is 5.
pub struct DiffSwitchMeta {
    /// The total number of difficulties represented, including those with no explicit values.
    pub num_difficulties: usize,
    /// Indices where at least one switch had a value.
    pub explicit_difficulties: BitSet32,
}

impl DiffSwitchMeta {
    pub fn new() -> Self { DiffSwitchMeta {
        num_difficulties: 0,
        explicit_difficulties: BitSet32::from_mask(0),
    }}

    /// Add explicit cases or increase the number of difficulties as necessary to make this
    /// compatible with the given switch.
    pub fn update<T>(&mut self, switch_cases: &DiffSwitchSlice<T>) {
        self.num_difficulties = self.num_difficulties.max(switch_cases.len());

        for (difficulty, case) in switch_cases.iter().enumerate() {
            if case.is_some() {
                self.explicit_difficulties.insert(difficulty as u32);
            }
        }
    }
}

/// Grab the corresponding item from difficulty cases.
pub fn select_diff_switch_case<T>(cases: &DiffSwitchSlice<T>, difficulty: u32) -> &T {
    assert!(difficulty < cases.len() as u32);
    (0..=difficulty as usize).rev()  // start from difficulty and look backwards
        .filter_map(move |i| cases[i].as_ref()).next()  // find first Some
        .expect("there's always an easy value")
}

pub fn explicit_difficulty_cases<T>(cases: &DiffSwitchSlice<T>) -> Vec<(BitSet32, &T)> {
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

impl DiffSwitchMeta {
    /// Get masks for each difficulty case based on how it is repeated.
    /// The input list of indices must be sorted.
    ///
    /// For instance, a switch like `(a:::b:)` will produce two masks, `0b111` (for `a`) and `0b11000` (for `b`).
    pub fn explicit_case_bitmasks(&self) -> impl Iterator<Item=BitSet32> {
        let mut stops = self.explicit_difficulties.into_iter().chain(core::iter::once(self.num_difficulties as u32));

        let mut prev = stops.next().expect("always at least one case");
        stops.map(move |stop| {
            debug_assert!(prev < stop, "explicit_difficulties not sorted, or bad len");
            let bitset = (prev..stop).collect();
            prev = stop;
            bitset
        })
    }

    pub fn switch_from_explicit_cases<T: Clone, Ts>(&self, explicit_cases: Ts) -> DiffSwitchVec<T>
    where
        Ts: IntoIterator<Item=T>,
        <Ts as IntoIterator>::IntoIter: ExactSizeIterator,
    {
        let explicit_cases = explicit_cases.into_iter();
        assert_eq!(explicit_cases.len(), self.explicit_difficulties.len());

        let mut out = vec![None; self.num_difficulties];
        for (difficulty, value) in self.explicit_difficulties.into_iter().zip(explicit_cases) {
            out[difficulty as usize] = Some(value);
        }
        out
    }
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
    let f = |difficulties: Vec<u32>, num_difficulties| DiffSwitchMeta {
        explicit_difficulties: difficulties.into_iter().collect(),
        num_difficulties,
    }.explicit_case_bitmasks();
    assert_eq!(
        f(vec![0, 1, 2], 3).collect::<Vec<_>>(),
        vec![m(1), m(2), m(4)],
    );
    assert_eq!(
        f(vec![0, 3], 5).collect::<Vec<_>>(),
        vec![m(0b111), m(0b11000)],
    );
}
