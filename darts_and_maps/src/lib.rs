#![feature(map_first_last)]

pub mod darts {

    use auto_ops::impl_op_ex; // to define multiplication
    use bit_set::BitSet;
    use gcd::Gcd;
    use rand::seq::SliceRandom;
    use rand::Rng;
    use std::collections::BTreeSet;
    use std::fmt;

    /* CONSTANTS SET BY HAND */
    pub type PermBitRep = u128;
    pub type DartBitRep = u8;
    pub type Dart = DartBitRep;
    pub const DEGREE: DartBitRep = 24; // number of darts permuted
    pub const LOG_DEGREE: DartBitRep = 5; // ⌈log₂(DEGREE)⌉
    pub const MASK: PermBitRep = 0b11111;
    pub const PERMBITREP_USED: usize = (DEGREE * LOG_DEGREE) as usize;
    pub const IDENTITY_ARR: [DartBitRep; DEGREE as usize] = [
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
    ];
    pub const DEGREE_ONES: u32 = 0b0000_0000_1111_1111_1111_1111_1111_1111;
    pub const ONLY_ONES: u32 = 0b1111_1111_1111_1111_1111_1111_1111_1111;

    pub fn bit_set_full_until_n(n: Dart) -> BitSet {
        debug_assert!(n <= DEGREE);

        let mut res: BitSet = BitSet::with_capacity(DEGREE as usize);
        for d in 0..n {
            res.insert(d as usize);
        }
        res
    }

    #[derive(Clone, PartialEq, Eq, Hash, Copy, PartialOrd, Ord)]
    pub struct DartArray {
        permutation: PermBitRep,
    }

    impl DartArray {
        pub fn is_bijection(&self) -> bool {
            self.is_injective_on(&bit_set_full_until_n(DEGREE))
                .is_some()
        }

        pub fn is_bijective_from_to(&self, domain: &BitSet, range: &BitSet) -> bool {
            debug_assert!(domain.len() == range.len());

            let mut range = range.clone();
            for d in domain.iter() {
                let d = d as Dart;
                if !range.contains(self.image(d) as usize) {return false;}
                range.remove(self.image(d) as usize);
            }
            return range.is_empty();
        }

        pub fn is_injective_on(&self, domain: &BitSet) -> Option<BitSet> {
            let mut range: BitSet = BitSet::with_capacity(DEGREE as usize);
            for d in domain.iter() {
                debug_assert!(d < DEGREE as usize);
                let i = self.image(d as DartBitRep);
                debug_assert!(i < DEGREE);
                if range.contains(i as usize) {
                    return None;
                } else {
                    range.insert(i as usize);
                }
            }
            return Some(range);
        }

        pub fn is_identity(&self) -> bool {
            debug_assert!(self.is_bijection());

            self == &Self::identity()
        }

        pub fn is_identity_on(&self, domain: &BitSet) -> bool {
            for d in domain.iter() {
                let d = d as Dart;
                if self.image(d) != d {
                    return false;
                }
            }
            true
        }

        pub fn is_involution(&self) -> bool {
            debug_assert!(self.is_bijection());

            self.order() <= 2
        }

        pub fn is_involution_on(&self, domain: &BitSet) -> bool {
            for d in domain.iter() {
                let d = d as Dart;
                if !domain.contains(self.image(d) as usize) {return false;}
                if self.image(self.image(d)) != d {return false;}
            }
            return true;
        }


        pub fn random_permutation<R>(r: &mut R) -> DartArray
        where
            R: Rng,
        {
            // from https://docs.rs/rand/0.7.3/rand/seq/trait.SliceRandom.html#tymethod.shuffle
            let mut y: [DartBitRep; DEGREE as usize] = IDENTITY_ARR;
            y.shuffle(r);
            DartArray::from(y.to_vec())
        }
        

        pub fn random_permutation_until<R>(r: &mut R, o: DartBitRep) -> DartArray
        where
            R: Rng,
        {
            // o is the number of darts permuted randomly (the ones above are leftfixed)
            debug_assert!(o <= DEGREE);

            let mut y: Vec<DartBitRep> = (0..o).collect();
            y.shuffle(r);
            let mut rest: Vec<DartBitRep> = (o..DEGREE as DartBitRep).collect::<Vec<DartBitRep>>();
            y.append(&mut rest);
            DartArray::from(y)
        }

        pub fn cycles_on(&self, domain: &BitSet) -> Vec<Vec<DartBitRep>> {
            assert!(self.is_bijective_from_to(domain, domain));

            let me = self;
            let mut cycles: Vec<Vec<DartBitRep>> = Vec::new();

            let mut remaining: BTreeSet<DartBitRep> = domain.iter().map(|x| x as Dart).collect();

            while let Some(origin) = remaining.pop_first() {
                let mut cycle = Vec::new();
                cycle.push(origin);

                let mut next = origin;
                while me.image(next) != origin {
                    next = me.image(next);
                    cycle.push(next);
                    remaining.remove(&next);
                }

                if cycle.len() > 1 {
                    // don't show fixed points
                    cycles.push(cycle);
                }
            }
            cycles
        }

        pub fn order_on(&self, domain: &BitSet) -> usize {
            assert!(self.is_bijective_from_to(domain, domain));
            
            let cycles = self.cycles_on(domain);
            cycles.iter().fold(1, |a, b| a * b.len() / a.gcd(b.len()))
        }

        pub fn order(&self) -> usize {
            assert!(self.is_bijection());
            let domain = bit_set_full_until_n(DEGREE);
            self.order_on(&domain)
        }

        pub fn set_kv(&mut self, k: DartBitRep, v: DartBitRep) {
            debug_assert!(k < DEGREE);
            debug_assert!(v < DEGREE);

            self.permutation &= !(MASK << (LOG_DEGREE * k));
            self.permutation |= (v as PermBitRep) << (LOG_DEGREE * k);
        }

        pub fn image(&self, x: DartBitRep) -> DartBitRep {
            debug_assert!(x < DEGREE);

            ((self.permutation >> ((LOG_DEGREE * x) as PermBitRep)) & MASK) as DartBitRep
        }
    
            
        // if not bijective, then the _first_ preimage if it exists, otherwise fails
        pub fn preimage(&self, x: DartBitRep) -> DartBitRep {
            
            debug_assert!(x < DEGREE);

            let mut perm = self.permutation;
            for y in 0..DEGREE {
                if (perm & MASK) as DartBitRep == x {
                    return y as DartBitRep;
                }
                perm >>= LOG_DEGREE;
            }
            unreachable!();
            // return 0;
        }

        
        fn to_vec(&self) -> Vec<DartBitRep> {
            let mut perm = self.permutation;
            let mut out: Vec<DartBitRep> = Vec::new();

            for _ in 0..DEGREE {
                out.push((perm & MASK as PermBitRep) as DartBitRep);
                perm >>= LOG_DEGREE;
            }
            out
        }
        

        pub fn multiply_with(&self, other: &Self) -> Self {
            let mut perm: PermBitRep = 0;
            for y in 0..DEGREE {
                perm |=
                    (other.image(self.image(y)) as PermBitRep) << (LOG_DEGREE * y as DartBitRep);
            }
            DartArray { permutation: perm }
        }

        pub fn multiply_with_bis(&self, other: &Self) -> Self {
            let mut prod: PermBitRep = 0;
            let mut me = self.permutation;
            let other = other.permutation;
            for _ in 0..DEGREE {
                prod >>= LOG_DEGREE;
                prod |= ((other >> LOG_DEGREE * (me & MASK as PermBitRep) as u8)
                    & MASK as PermBitRep)
                    << (PERMBITREP_USED - LOG_DEGREE as usize);
                me >>= LOG_DEGREE;
            }
            DartArray { permutation: prod }
        }

        pub fn inverse(&self) -> Self {
            assert!(self.is_bijection());
            let mut perm: PermBitRep = 0;
            for y in 0..DEGREE {
                perm |= (self.preimage(y) as PermBitRep) << (LOG_DEGREE * y);
            }
            DartArray { permutation: perm }
        }

        pub fn identity() -> Self {
            DartArray::from((0..DEGREE as DartBitRep).collect::<Vec<DartBitRep>>())
        }

        pub fn get_content(&self) -> PermBitRep {
            self.permutation
        }

        pub fn get_perm_array(&self) -> [DartBitRep; DEGREE as usize] {
            let mut array: [DartBitRep; DEGREE as usize] = [0; DEGREE as usize];
            for idx in 0..DEGREE {
                // not very optimized maybe…
                array[idx as usize] = self.image(idx as u8);
            }
            array
        }
    }

    impl fmt::Display for DartArray {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{:?}", self.to_vec())
        }
    }

    impl fmt::Debug for DartArray {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{:?}", self.to_vec())
        }
    }

    impl From<Vec<DartBitRep>> for DartArray {
        fn from(perm_vec: Vec<DartBitRep>) -> Self {
            assert!(perm_vec.len() <= DEGREE as usize);

            let mut perm: PermBitRep = 0;
            for (idx, val) in perm_vec.iter().enumerate() {
                assert!(*val < DEGREE);
                //println!("{:#066b}",perm_vec[y]);
                perm |= (*val as PermBitRep) << (LOG_DEGREE * idx as DartBitRep);
                //println!("{:#066b}",perm);
            }
            // Assuming the input vec is too short, we fill the rest with fixed points
            for idx in perm_vec.len()..DEGREE as usize {
                perm |= (idx as PermBitRep) << (LOG_DEGREE * idx as DartBitRep);
            }
            DartArray { permutation: perm }
        }
    }

    impl_op_ex!(*|a: &DartArray, b: &DartArray| -> DartArray { a.multiply_with_bis(b) });

    #[derive(Clone, Debug)]
    pub struct SubPermutation {
        /* For simplicity's sake the domain is always supposed to be a subset of 0..perm.len()
         * and if d is not in the domain, then perm[d] should not be accessed */
        pub perm: DartArray,
        domain: BitSet,
        range: BitSet,
    }

    impl From<Vec<usize>> for SubPermutation {
        /* By default the domain is 0..perm.len() */

        fn from(perm: Vec<usize>) -> Self {
            let mut domain: BitSet = BitSet::with_capacity(DEGREE as usize);
            let mut range: BitSet = BitSet::with_capacity(DEGREE as usize);
            for (k, v) in perm.iter().enumerate() {
                domain.insert(k);
                range.insert(*v as usize);
            }
            let perm: Vec<Dart> = perm.iter().map(|a| *a as Dart).collect();
            let p = SubPermutation {
                perm: DartArray::from(perm),
                domain: domain, // TODO this is ugly
                range: range,
            };
            p
        }
    }

    impl From<Vec<u8>> for SubPermutation {
        /* By default the domain is 0..perm.len() */

        fn from(perm: Vec<u8>) -> Self {
            let perm: Vec<usize> = perm.iter().map(|a| *a as usize).collect();
            Self::from(perm)
        }
    }
    impl From<Vec<i32>> for SubPermutation {
        /* By default the domain is 0..perm.len() */

        fn from(perm: Vec<i32>) -> Self {
            let perm: Vec<usize> = perm.iter().map(|a| *a as usize).collect();
            Self::from(perm)
        }
    }

    impl From<(Vec<Dart>, BitSet, BitSet)> for SubPermutation {
        /* By default the domain is 0..perm.len() */
        fn from((perm, domain, range): (Vec<Dart>, BitSet, BitSet)) -> Self {
            let p = SubPermutation {
                perm: DartArray::from(perm),
                domain: domain, // TODO this is ugly
                range: range,
            };
            p
        }
    }

    impl From<Vec<Vec<usize>>> for SubPermutation {
        /* Disjoint cycle decomposition */
        fn from(cycles: Vec<Vec<usize>>) -> SubPermutation {
            let mut domran: BitSet = BitSet::with_capacity(DEGREE as usize);
            domran.extend(cycles.iter().flatten().map(|a| *a));
            let max: usize = *cycles.iter().flatten().max().unwrap();

            let mut perm_vec: Vec<Dart> = (0..max as Dart).collect();
            for cycle in cycles {
                for i in 0..cycle.len() {
                    perm_vec[cycle[i]] = cycle[(i + 1) % cycle.len()] as Dart;
                }
            }
            SubPermutation::from((perm_vec, domran.clone(), domran))
        }
    }

    impl fmt::Display for SubPermutation {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let stringed: Vec<String> = self
                .perm
                .get_perm_array()
                .iter()
                .map(|x| {
                    if self.domain.contains(*x as usize) {
                        x.to_string() + ","
                    } else {
                        "_".to_owned() + ","
                    }
                })
                .collect();
            let mystring: String = stringed.concat();
            write!(f, "[{}]", mystring)
        }
    }

    impl_op_ex!(*|a: &SubPermutation, b: &SubPermutation| -> SubPermutation { a.prod(b) });

    impl PartialEq for SubPermutation {
        fn eq(&self, other: &Self) -> bool {

            let result = self.domain == other.domain
                && self.range == other.range
                && self
                    .domain
                    .iter()
                    .all(|d| self.image(d as Dart) == other.image(d as Dart));
            result
        }
    }
    impl Eq for SubPermutation {}

    // Ci-dessus permet de pas faire …
    //impl Mul for SubPermutation {}

    impl SubPermutation {
        pub fn random_in<R>(r: &mut R, number_darts: Dart) -> SubPermutation
        where
            R: Rng,
        {
            let p = DartArray::random_permutation_until(r, number_darts);
            SubPermutation {
                perm: p,
                domain: bit_set_full_until_n(number_darts),
                range: bit_set_full_until_n(number_darts),
            }
        }

        pub fn domain_contains(&self, d: Dart) -> bool {
            self.domain.contains(d as usize)
        }
        pub fn range_contains(&self, d: Dart) -> bool {
            self.range.contains(d as usize)
        }
        pub fn domain(&self) -> &BitSet {
            &self.domain
        }

        pub fn domain_complemented(&self, universe: &BitSet) -> BitSet {
            universe.difference(self.domain()).collect()
        }
        pub fn range_complemented(&self, universe: &BitSet) -> BitSet {
            universe.difference(self.range()).collect()
        }

        pub fn range(&self) -> &BitSet {
            &self.range
        }

        pub fn get_vec(&self) -> [Dart; DEGREE as usize] {
            self.perm.get_perm_array()
        }

        pub fn prod(&self, other: &SubPermutation) -> SubPermutation {
            SubPermutation {
                perm: self.perm * other.perm,
                domain: self.domain.clone(),
                range: self.range.clone(),
            }
        }

        pub fn extend_domran(&self, extension: BitSet) -> SubPermutation {
            let mut extended_domran = self.domain.clone();
            extended_domran.union_with(&extension);

            SubPermutation {
                perm: self.perm.clone(),
                domain: extended_domran.clone(),
                range: extended_domran.clone(),
            }
        }

        pub fn restrict_domran(&self, restriction: BitSet) -> SubPermutation {
            SubPermutation {
                perm: self.perm.clone(),
                domain: restriction.clone(),
                range: restriction,
            }
        }

        pub fn image(&self, dart: Dart) -> Dart {
            self.perm.image(dart)
        }

        pub fn preimage(&self, dart: Dart) -> Dart {
            self.perm.preimage(dart)
        }

        pub fn inverse(&self) -> SubPermutation {
            SubPermutation {
                perm: self.perm.inverse(),
                domain: self.range.clone(),
                range: self.domain.clone(),
            }
        }

        pub fn conjugate(&self, by: &SubPermutation) -> SubPermutation {
            by.inverse() * self * by
        }

        pub fn rename(&self, by: &SubPermutation) -> SubPermutation {
            self.conjugate(by)
        }

        pub fn is_identity(&self) -> bool {
            self.domain
                .iter()
                .all(|d| d as Dart == self.image(d as Dart))
        }

        pub fn is_involution(&self) -> bool {
            (self * self).is_identity()
        }

        pub fn has_no_fixed_points(&self) -> bool {
            self.domain
                .iter()
                .all(|d| d as Dart != self.image(d as Dart))
        }

        pub fn compute_orbits(&self) -> BTreeSet<BitSet> {
            let mut my_orbits = BTreeSet::<BitSet>::new();

            let mut remaining: BTreeSet<Dart> = self.domain.iter().map(|x| x as Dart).collect();

            while let Some(dart) = remaining.pop_first() {
                let mut orbit = BitSet::with_capacity(DEGREE as usize);
                orbit.insert(dart as usize);

                let mut next = dart;
                while self.image(next) != dart {
                    next = self.image(next);
                    orbit.insert(next as usize);
                    remaining.remove(&next);
                }

                my_orbits.insert(orbit);
            }
            //println!("… and they are {:?}", my_orbits);
            my_orbits
        }

        pub fn compute_orbits_reps(&self) -> DartArray {
            let mut orbits_reps = self.perm.clone();
            for d in self.domain().iter() {
                let d = d as Dart;
                let mut dd = orbits_reps.image(d);
                while dd > d {
                    dd = orbits_reps.image(dd);
                }
                orbits_reps.set_kv(d,dd);
            }
            orbits_reps
        }

        pub fn add_kv(&self, from: Dart, to: Dart) -> Self {
            assert!(!(self.domain.contains(from as usize)));
            assert!(!(self.range.contains(to as usize)));

            let mut perms = self.perm.clone();
            perms.set_kv(from, to);
            let mut domain = self.domain.clone();
            let mut range = self.range.clone();
            domain.insert(from as usize);
            range.insert(to as usize);
            SubPermutation {
                perm: perms,
                domain: domain,
                range: range,
            }
        }

        pub fn set_kv(&mut self, from: Dart, to: Dart) {
            assert!(!(self.domain.contains(from as usize)));
            assert!(!(self.range.contains(to as usize)));

            self.perm.set_kv(from, to);
            self.domain.insert(from as usize);
            self.range.insert(to as usize);
        }
    }

    pub fn join_partitions_reps(left: &DartArray, right: &DartArray, universe: &BitSet) -> DartArray {
        let mut out = left.clone();
        for d in universe.iter() {
            let d = d as Dart;
            let left_rep = out.image(d);
            let right_rep = right.image(d);
            debug_assert!(left_rep <= d || right_rep <= d);
            if left_rep < right_rep {
                // do nothing I think?
            } else if right_rep < left_rep {
                for d2 in universe.iter().filter(|d2| right_rep <= *d2 as Dart && *d2 as Dart <= d) {
                    let d2 = d2 as Dart;
                    if out.image(d2) == left_rep {
                        out.set_kv(d2, right_rep)
                    } 
                }
            } else /* if left_rep = right_rep */ {
                // do nothing I think
            }
                
            
        }
        out
    }

    pub fn join_partitions(
        left: &BTreeSet<BitSet>,
        right: &BTreeSet<BitSet>,
        universe: &BitSet,
    ) -> BTreeSet<BitSet> {
        let mut joined: BTreeSet<BitSet> = left.union(right).cloned().collect();
        for d in universe.iter() {
            let containing_d = joined.clone().into_iter().filter(|orbit| orbit.contains(d));
            let mut union = BitSet::with_capacity(universe.len());
            for o in containing_d {
                union.extend(&o);
                joined.remove(&o);
            }
            joined.insert(union);
        }
        joined
    }

    impl From<(Vec<Dart>, Dart)> for SubPermutation {
        /* By default the domain is 0..perm.len() */
        fn from((p, domain_max): (Vec<Dart>, Dart)) -> Self {
            SubPermutation {
                perm: DartArray::from(p),
                domain: bit_set_full_until_n(domain_max),
                range: bit_set_full_until_n(domain_max),
            }
        }
    }
}

pub mod map {

    use super::darts::join_partitions;
    use super::darts::Dart;
    use super::darts::SubPermutation;
    use super::darts::*;
    use bit_set::BitSet;
    use std::collections::BTreeSet;
    use std::fmt;
    use std::ops::Index;

    #[derive(Clone, Debug)]
    pub struct Map {
        pub permutations: Vec<SubPermutation>,
    }

    impl From<Vec<SubPermutation>> for Map {
        /* By default the domain is 0..perm.len() */
        fn from(perms: Vec<SubPermutation>) -> Self {
            Map {
                permutations: perms,
            }
        }
    }

    impl Index<usize> for Map {
        type Output = SubPermutation;

        fn index(&self, i: usize) -> &Self::Output {
            debug_assert!(self.len() > i, "Map should have enough permutations");
            &(self.permutations[i])
        }
    }

    impl fmt::Display for Map {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            for s in self.perms() {
                let _ = write!(f, "{}", s);
                let _ = write!(f, ",");
            }
            Ok(()) // should manage failures of the other writes instead of dismissing the result
        }
    }

    impl Map {

        pub fn number_darts(&self) -> usize {
            debug_assert!(self.len() > 0);
            let n = self[0].domain().len();
            for i in 0..self.len() {
                debug_assert!(self[i].domain().len() == n);
                debug_assert!(self[i].range().len() == n);
            }
            n
        }

        pub fn perms(&self) -> &Vec<SubPermutation> {
            &self.permutations
        }

        pub fn push(&mut self, p: SubPermutation) {
            self.permutations.push(p)
        }

        fn len(&self) -> usize {
            self.permutations.len()
        }


        /// Checks isomorphism
        /// by trying to construct bijections
        pub fn is_isomorphic(&self, other: &Map) -> bool {
            
            /// Given the maps `map1` and `map2`, a bijection `p` from a subset of darts of `map1` to a
            /// subset of darts of `map2` and a candidate extension `source`↦`target` of `p`,
            /// returns `None` if this extension is invalid (in the sense that it cannot be extended into a valid bijection) and `Some(p')` if `p'` extends `p` with
            /// `source`↦`target` and whatever other assignments follow from this one.
            fn try_extending_partial_isomorphism(
                p: &SubPermutation,
                map1: &Map,
                map2: &Map,
                source: Dart,
                target: Dart,
            ) -> Option<SubPermutation> {

                let mut p = p.clone();

                // `new` contains all assignments that follow from `source`↦`target`.
                // Say `source` is connected through a red edge to s2 and `target` to t2
                // Then necessarily we must have s2↦t2, and the pair s2↦t2 will be added to `new`
                // 
                // At first, only `sourc`e↦`target` is contained in `new`
                let mut new: Vec<(Dart, Dart)> = Vec::new();
                new.push((source, target));

                // As long as there is something in `new`
                while let Some((s, t)) = new.pop() {
                    
                    // By convention, if it's in `new`, it's actually  a new assignment
                    debug_assert!(
                        !(p.domain_contains(s) && p.image(s) == t),
                        "The partial isom {:?} shouldn't already be defined as {} on {}",
                        p,
                        t,
                        s
                    );
                    
                    // If `s` is arleady in the domain of `p`, then the assignment `s↦t` clashes
                    // with some other assignment, hence `p` cannot be extended with
                    // `source`↦`target` 
                    if p.domain_contains(s) {
                        return None;
                    }

                    // Same idea as above
                    if p.range_contains(t) {
                        return None;
                    }

                    // Otherwise, we add the assignment to `p`
                    p.set_kv(s, t);
                    
                    // And for each permutation in the map, we add the pairs in new that "follow"
                    // from `s`↦`t`
                    // That is, say the maps are (α,β) and (α',β').
                    // If s↦t, then necessarily αs ↦ α't and βs ↦ β't, so we add those assignments
                    // (if they are not already in `new` or in `p`)
                    for (a1_i, a2_i) in map1.perms().iter().zip(map2.perms().iter()).filter(|(a1_i,a2_i)| a1_i.domain_contains(s) && a2_i.domain_contains(t)) {
                        let new_s = a1_i.image(s);
                        let new_t = a2_i.image(t);
                        if !(p.domain_contains(new_s) && p.image(new_s) == new_t)
                            && !new.contains(&(new_s, new_t))
                        {
                            new.push((new_s, new_t));
                        }
                    }
                }
                
                // If nothing failed and all assignments that follow from `source`↦`target` have
                // been added to `p`, we return the extension
                return Some(p);
            }



            // We can now try to build the isomorphism

            // We start with an empty bijection
            let empty_partial_isomorphism = SubPermutation::from((
                vec![],
                BitSet::with_capacity(DEGREE as usize),
                BitSet::with_capacity(DEGREE as usize),
            ));

            // `partial_isomorphisms` will store all candidate partial isomorphisms (bijections
            // from subsets of darts to subsets of darts that commute as needed with the
            // permutationsin the maps)
            let mut partial_isomorphisms = vec![empty_partial_isomorphism];

            // As long as there is one, `p`
            while let Some(p) = partial_isomorphisms.pop() {
                let full = self[0].domain().clone();
                let not_in_domain = p.domain_complemented(&full);
                let not_in_range = p.range_complemented(&full);

                
                match not_in_domain.iter().next() {
                    None => { 
                        // if it is complete, we have found an isomorphism
                        /*
                        debug_assert!(
                            self.perms()
                            .iter()
                            .zip(other.perms().iter())
                            .map(|(x,y)| {
                                (x*p.clone(),p.clone()*y)
                            })
                            .all(|(x,y)| x == y)
                        );*/
                        return true;
                    }
                    Some(source) => {
                        // otherwise, we take some source dart `source` in those not in the domain of `p`, and try to extend `p` with every dart not in the range of `p`
                        for target in not_in_range.iter() {
                            match try_extending_partial_isomorphism(
                                &p,
                                self,
                                other,
                                source as Dart,
                                target as Dart,
                            ) {
                                Some(p_extended) => partial_isomorphisms.push(p_extended),
                                None => {}
                            }
                        }
                    }
                }
            }
            
            // No isomorphism found :(
            return false;
        }
        
        /// Returns the orbits of self, which should be thesame as the connected_components_domains
        pub fn orbits(&self) -> BTreeSet<BitSet> {
            let fst = &self[0];
            let rst = &self.perms()[1..];
            let all_darts = self[0].domain();
            rst.iter()
                .map(|p| p.compute_orbits())
                .fold(fst.compute_orbits(), |x, y| join_partitions(&x, &y, all_darts))
        }
        
        /// Computes the vertex links (as 2D-maps i.e. ribbon graph) of self.
        /// TODO: check that the number of connected components of link is exactly the number of
        /// vertices
        pub fn link_of_spehner_map(&self) -> Map {
            let a = self[0].clone();
            let b = self[1].clone();
            let c = self[2].clone();
            // c*b*a = vertices = sigma, c = edges = alpha 
            let link = Map::from(vec![c.clone() * (b * a), c]);
            link
        }

        /// Returns the connected components of self, as Spehner maps
        pub fn connected_components_maps(&self) -> Vec<Map> {
            let orbits = self.orbits();
            orbits
                .iter()
                .map(|orb| {
                    Map::from(
                        self.perms()
                            .iter()
                            .map(|p| p.restrict_domran(orb.clone()))
                            .collect::<Vec<SubPermutation>>(),
                    )
                })
                .collect::<Vec<Map>>()
        }

        /// Returns the domains of the connected components of self, hence a set of set of darts
        pub fn connected_components_domains(&self) -> BTreeSet<BTreeSet<Dart>> {
            let mut remaining: BTreeSet<Dart> =
                self[0].domain().iter().map(|a| a as Dart).collect();
            let mut connected_components: BTreeSet<BTreeSet<Dart>> = BTreeSet::new();

            while let Some(base) = remaining.pop_first() {
                let mut connected: BTreeSet<Dart> = BTreeSet::new();
                let mut new: BTreeSet<Dart> = BTreeSet::new();
                new.insert(base);
                while let Some(d) = new.pop_first() {
                    connected.insert(d);

                    for a in self.perms() {
                        if !connected.contains(&a.image(d)) {
                            remaining.remove(&a.image(d));
                            new.insert(a.image(d));
                        }
                    }
                }
                connected_components.insert(connected);
            }

            connected_components
        }


        /// Computes the Euler characteristic of a given connected 2D map (aka ribbon graph)
        pub fn two_dim_map_euler_char(&self) -> i32 {
            let sigma = &self[0];
            let alpha = &self[1];
            let phi = sigma.inverse() * alpha;

            fn num_orbits(p: &SubPermutation) -> i32 {
                p.compute_orbits().len() as i32
            }

            // For a closed surface Σ: χ(Σ) = 2 - 2g(Σ) where χ is Euler char and g is genus
            num_orbits(&phi) - num_orbits(&alpha) + num_orbits(&sigma)
        }

        /// Computes the Euler characteristics of the vertex links of a given connected Spehner map
        pub fn vertex_links_euler_char(&self) -> Vec<i32> {
            let links = self.link_of_spehner_map();
            links.connected_components_maps()
                .iter()
                .map(|conn| {
                    debug_assert!(conn.is_connected()); 
                    conn.two_dim_map_euler_char()
                })
                .collect()
        }

        /// Checks whether the map self is connected (underlying trivalent graph is connected)
        pub fn is_connected(&self) -> bool {
            let mut connected: BTreeSet<Dart> = BTreeSet::new();
            let mut new: BTreeSet<Dart> = BTreeSet::new();

            let d0 = self[0].domain().iter().next().unwrap();
            new.insert(d0 as Dart);
            while let Some(d) = new.pop_first() {
                connected.insert(d);

                for a in self.perms() {
                    if !connected.contains(&a.image(d)) {
                        new.insert(a.image(d));
                    }
                }
            }

            return connected.len() == self.number_darts();
        }
    }
}

#[cfg(test)]
mod tests {

    use super::map::*;
    use super::darts::*;
    use bit_set::*;
    use bit_vec::BitVec;

    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }

    #[test]
    fn only_identity_is_identity() {
        assert!(DartArray::identity().is_identity());
        for i in 0..40 {
            let r = DartArray::random_permutation(&mut rand::thread_rng());
            if r.is_identity() {
                assert_eq!(r, DartArray::identity());
            } else {
                assert_ne!(r, DartArray::identity());
            }
        }
    }

    #[test]
    fn order_is_correct() {
        // Fixed tests
        let identity = DartArray::from(vec![0, 1, 2, 3, 4, 5, 6, 7]);
        let involution_a = DartArray::from(vec![1, 0, 2, 3, 4, 5, 6, 7]);
        let involution_b = DartArray::from(vec![1, 0, 3, 2, 4, 5, 6, 7]);
        let involution_c = DartArray::from(vec![0, 1, 3, 2, 4, 5, 6, 7]);
        let three_cycle_a = DartArray::from(vec![1, 2, 0, 3, 4, 5, 6, 7]);
        let three_cycle_z = DartArray::from(vec![1, 2, 0, 3, 4, 6, 7, 5]);
        assert_eq!(1, identity.order(), "identity has order 1");
        assert_eq!(2, involution_a.order(), "involution has order 2");
        assert_eq!(2, involution_b.order(), "involution has order 2");
        assert_eq!(2, involution_c.order(), "involution has order 2");
        assert_eq!(3, three_cycle_a.order());
        assert_eq!(6, (three_cycle_z * &involution_a).order());

        // Random tests
        for i in 0..40 {
            let r = DartArray::random_permutation(&mut rand::thread_rng());

            assert_eq!(&r.order(), &r.inverse().order());

            let order_r = r.order();
            let mut power = r.clone();

            // println!("r is     {:?}", &r);
            // println!("order is {}", &order_r);

            for i in 0..order_r - 1 {
                assert!(!(power == DartArray::identity()));
                power = power * &r;
            }
            assert!(power == DartArray::identity());
        }
    }

    #[test]
    fn multiplication_behaves_well() {
        for i in 0..40 {
            let r = DartArray::random_permutation(&mut rand::thread_rng());
            let s = DartArray::random_permutation(&mut rand::thread_rng());

            assert_eq!(&s.multiply_with(&r), &s.multiply_with_bis(&r));
            assert_eq!(&s.inverse() * &s, DartArray::identity());
            assert_eq!(&s * &s.inverse(), DartArray::identity());
        }
    }

    #[test]
    fn test_orbits() {
        for i in 0..40 {
            let r = DartArray::random_permutation(&mut rand::thread_rng());
        }
    }

    #[test]
    fn random_in_behaves() {
        let r = &mut rand::thread_rng();

        for o in 0..DEGREE {
            for _ in 0..100 {
                let p = DartArray::random_permutation_until(r, o);
                for d in 0..o as DartBitRep {
                    assert!(p.image(d) < o as DartBitRep);
                }

                for d in o as DartBitRep..DEGREE {
                    assert_eq!(p.image(d), d);
                }
            }
        }
    }

    /*



    #[test]
    fn bunch_of_illegal_actions_should_be_illegal() {
        let three_ones = vec![1, 1, 1];
        let too_high = vec![1, 2, 3];
        let not_bij = vec![1, 1, 2];

        let id_three = vec![0, 1, 2];

        let mut too_far = BitSet::with_capacity(DEGREE as usize);
        too_far.insert(3);
        let mut last = BitSet::with_capacity(DEGREE as usize);
        last.insert(2);
        let mut last_two = BitSet::with_capacity(DEGREE as usize);
        last_two.insert(1);
        last_two.insert(2);
        let mut all = BitSet::with_capacity(DEGREE as usize);
        all.insert(0);
        all.insert(1);
        all.insert(2);

        assert!(!vec_darts_acts_on_domain(&id_three, &too_far),);

        assert!(!vec_darts_acts_on_domain(&too_high, &all),);

        assert!(!vec_darts_acts_on_domain(&too_high, &last_two),);
        assert!(!vec_darts_acts_on_domain(&not_bij, &all),);
    }

    #[test]
    fn bunch_of_legal_actions_should_be_legal() {
        let three_ones = vec![1, 1, 1];
        let too_high = vec![1, 2, 3];
        let not_bij = vec![1, 1, 2];

        let id_three = vec![0, 1, 2];

        let mut last = BitSet::with_capacity(DEGREE as usize);
        last.insert(2);
        let mut last_two = BitSet::with_capacity(DEGREE as usize);
        last_two.insert(1);
        last_two.insert(2);
        let mut all = BitSet::with_capacity(DEGREE as usize);
        all.insert(0);
        all.insert(1);
        all.insert(2);

        assert!(vec_darts_acts_on_domain(&id_three, &all),);
        assert!(vec_darts_acts_on_domain(&id_three, &last_two),);
        assert!(vec_darts_acts_on_domain(&id_three, &last),);
        assert!(vec_darts_acts_on_domain(&not_bij, &last_two),);
    }

    #[test]
    #[should_panic]
    fn three_ones_not_permutation() {
        let three_ones = vec![1, 1, 1];
        let p = SubPermutation::from(three_ones);
    }

    #[test]
    fn three_ones_permutation_when_restricted_to_one() {
        let three_ones = vec![1, 1, 1];
        let mut domain = BitSet::with_capacity(DEGREE as usize);
        domain.insert(1);
        let p = SubPermutation::from((three_ones, domain));
        assert!(true)
    }

    #[test]
    #[should_panic]
    fn three_ones_not_permutation_when_restricted_elsewhere() {
        let three_ones = vec![1, 1, 1];
        let mut domain = BitSet::with_capacity(DEGREE as usize);
        domain.insert(0);
        let p = SubPermutation::from((three_ones, domain));
        assert!(true)
    }

    */

    #[test]
    fn preimages() {
        let some_permutations_vec: Vec<Vec<Dart>> = vec![
            vec![0, 1, 2, 3, 4],
            vec![1, 2, 3, 0, 5, 4, 6, 9, 7, 8],
            vec![1, 3, 2, 0, 5, 4, 6, 9, 7, 8],
            vec![1, 3, 2, 0],
            vec![3, 2, 1, 0],
        ];
        let some_permutations = some_permutations_vec
            .into_iter()
            .map(|x| SubPermutation::from(x.clone()));

        for p in some_permutations {
            for d in p.domain().iter() {
                let d = d as Dart;
                assert_eq!(d, p.image(p.preimage(d)));
                assert_eq!(d, p.preimage(p.image(d)));
            }
        }
    }

    #[test]
    fn inverses() {
        let mut conj: Vec<Dart> = vec![1, 2, 3, 0, 5, 4, 6, 9, 7, 8];
        let c = SubPermutation::from(conj);

        assert!(((&c) * (&c.inverse())).is_identity());
        assert!(((&c.inverse()) * (&c)).is_identity());
    }

    #[test]
    fn involutions() {
        let mut perm: Vec<Dart> = (0..10).collect::<Vec<Dart>>();
        perm.reverse();
        let p = SubPermutation::from(perm);

        assert!(p.is_involution(), "Obvious involution should be one.");

        let mut conj: Vec<Dart> = vec![1, 2, 3, 0, 5, 4, 6, 9, 7, 8];
        let c = SubPermutation::from(conj);

        println!("{:?}", p.conjugate(&c));

        assert!(p.conjugate(&c).is_involution(), "Its conjugate also.");
        assert!(!(p * c).is_involution());
    }

    #[test]
    fn orbits() {
        let mut conj: Vec<Dart> = vec![1, 2, 3, 0, 5, 4, 6, 9, 7, 8];
        let c = SubPermutation::from(conj);

        let orbits_c = c.compute_orbits();
        println!("{:?}", orbits_c);
        assert_eq!(orbits_c.len(), 4);

        for o in orbits_c {
            println!("{}", c.restrict_domran(o));
        }

        let id: Vec<Dart> = (0..10).collect();
        assert_eq!(SubPermutation::from(id).compute_orbits().len(), 10);
    }
    #[test]
    fn join_partitions_behaves() {
        let id = SubPermutation::from(vec![0, 1, 2, 3, 4, 5]);
        let tran = SubPermutation::from(vec![5, 4, 3, 2, 1, 0]);
        let cycle = SubPermutation::from(vec![1, 2, 3, 4, 5, 0]);
        let two = SubPermutation::from(vec![1, 2, 0, 4, 5, 3]);

        assert_eq!(
            3,
            join_partitions(
                &id.compute_orbits(),
                &tran.compute_orbits(),
                &bit_set_full_until_n(6)
            )
            .len()
        );
        assert_eq!(
            6,
            join_partitions(
                &id.compute_orbits(),
                &id.compute_orbits(),
                &bit_set_full_until_n(6)
            )
            .len()
        );
        assert_eq!(
            1,
            join_partitions(
                &two.compute_orbits(),
                &tran.compute_orbits(),
                &bit_set_full_until_n(6)
            )
            .len()
        );

        assert_eq!(
            1,
            join_partitions(
                &two.compute_orbits(),
                &tran.compute_orbits(),
                &bit_set_full_until_n(6)
            )
            .len()
        );
    }

    #[test]
    fn connected_components_behaves() {}

    #[test]
    fn is_isomorphic_behaves() {
        let r = &mut rand::thread_rng();
        for i in 0..10 {
            for number_darts in vec![10, 12, 14, 20] {
                let a1 = SubPermutation::random_in(r, number_darts);
                let b1 = SubPermutation::random_in(r, number_darts);
                let c1 = SubPermutation::random_in(r, number_darts);

                let conj = SubPermutation::random_in(r, number_darts);

                let a2 = a1.rename(&conj);
                let b2 = b1.rename(&conj);
                let c2 = c1.rename(&conj);

                let map1 = Map {
                    permutations: vec![a1.clone(), b1.clone(), c1.clone()],
                };
                let map2 = Map {
                    permutations: vec![a2, b2, c2],
                };

                assert!(map1.is_isomorphic(&map2));
                assert_eq!(
                    map1.connected_components_domains().len(),
                    map2.connected_components_domains().len()
                );

                let another_map = Map {
                    permutations: vec![c1, a1, b1],
                }; // this one will probably be non_isomorphic

                if another_map.connected_components_domains().len()
                    != map2.connected_components_domains().len()
                {
                    assert!(!another_map.is_isomorphic(&map1));
                    assert!(!another_map.is_isomorphic(&map2));
                }
            }
        }
    }
}
