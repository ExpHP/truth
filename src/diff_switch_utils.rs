use crate::bitset::BitSet32;

/// A Vec containing data per case of a diff switch.  Data is only held in the explicitly-provided
/// cases, and the others are `None`.
///
/// If the length is 1, this does not represent a diff switch, but rather a scalar value.
pub type DiffSwitchVec<T> = Vec<Option<T>>;
/// Slice form of DiffSwitchVec.
pub type DiffSwitchSlice<T> = [Option<T>];

/// An alternate form of [`DiffSwitchVec`] which does not allocate for the single-value (scalar) case.
///
/// FIXME: Benchmark against one that is simply backed by DiffSwitchVec, but provides the same helper methods.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MaybeDiffSwitch<T> {
    /// An actual diff switch.  Must have len `>= 2`.  (it is a logic error to construct this otherwise)
    DiffSwitch(DiffSwitchVec<T>),
    Scalar(T),
}

impl<T> MaybeDiffSwitch<T> {
    // pub fn into_diff_switch(self) -> Option<DiffSwitchVec<T>> {
    //     match self {
    //         MaybeDiffSwitch::DiffSwitch(vec) => Some(vec),
    //         MaybeDiffSwitch::Scalar(_) => None,
    //     }
    // }
    //
    pub fn as_diff_switch(&self) -> Option<&DiffSwitchSlice<T>> {
        match self {
            MaybeDiffSwitch::DiffSwitch(vec) => Some(vec),
            MaybeDiffSwitch::Scalar(_) => None,
        }
    }

    pub fn easy_value(&self) -> &T {
        match self {
            MaybeDiffSwitch::Scalar(x) => x,
            MaybeDiffSwitch::DiffSwitch(vec) => vec[0].as_ref().expect("no easy value?!"),
        }
    }

    // #[track_caller]
    // pub fn expect_scalar(self) -> T {
    //     match self {
    //         MaybeDiffSwitch::DiffSwitch(_) => panic!("expect_scalar called on a diff switch"),
    //         MaybeDiffSwitch::Scalar(x) => x,
    //     }
    // }

    pub fn as_scalar(&self) -> Option<&T> {
        match self {
            MaybeDiffSwitch::Scalar(x) => Some(x),
            MaybeDiffSwitch::DiffSwitch(_) => None,
        }
    }

    pub fn iter_explicit_values(&self) -> impl Iterator<Item=&T> + '_ {
        match self {
            MaybeDiffSwitch::Scalar(x) => Box::new(core::iter::once(x)) as Box<dyn Iterator<Item=_>>,
            MaybeDiffSwitch::DiffSwitch(args) => Box::new(args.iter().filter_map(|opt| opt.as_ref())),
        }
    }

    /// Produce an iterator which has 1 item in the scalar case, or 2+ items for a diff switch.
    ///
    /// The [`FromIterator`] impl has matching behavior, so that you can use these two methods to
    /// map from one [`MaybeDiffSwitch`] to another of the same shape.
    pub fn iter(&self) -> impl Iterator<Item=Option<&T>> + '_ {
        match self {
            MaybeDiffSwitch::Scalar(x) => {
                Box::new(core::iter::once(Some(x))) as Box<dyn Iterator<Item=_>>
            },
            MaybeDiffSwitch::DiffSwitch(cases) => {
                assert!(cases.len() > 1, "invalid diff switch detected!");
                Box::new(cases.iter().map(|opt| opt.as_ref()))
            },
        }
    }

    // note: Can't impl Index due to lack of Option in Scalar
    pub fn index(&self, index: usize) -> Option<&T> {
        match self {
            MaybeDiffSwitch::Scalar(x) => {
                assert_eq!(index, 0, "index {} out of range for len 1", index);
                Some(x)
            },
            MaybeDiffSwitch::DiffSwitch(cases) => cases[index].as_ref(),
        }
    }
}

/// Constructs [`MaybeDiffSwitch::Scalar`] from 1 item, or [`MaybeDiffSwitch::DiffSwitch`] from more.
impl<T> FromIterator<Option<T>> for MaybeDiffSwitch<T> {
    fn from_iter<Ts: IntoIterator<Item=Option<T>>>(iter: Ts) -> Self {
        let mut iter = iter.into_iter();
        let first = iter.next().expect("diff switch had zero items!").expect("no easy value?!");

        if let Some(second) = iter.next() {
            let mut vec = vec![Some(first), second];
            vec.extend(iter);
            MaybeDiffSwitch::DiffSwitch(vec)
        } else {
            MaybeDiffSwitch::Scalar(first)
        }
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
