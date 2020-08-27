#![feature(map_first_last)]
#![feature(test)]
use bit_set::BitSet;
use rayon::prelude::*;
use std::env;
use std::time::SystemTime;

use darts_and_maps::map::Map;
use darts_and_maps::darts::bit_set_full_until_n;
use darts_and_maps::darts::join_partitions;
use darts_and_maps::darts::Dart;
use darts_and_maps::darts::DartArray;
use darts_and_maps::darts::SubPermutation;
use darts_and_maps::darts::DEGREE;

/*

  The definition of 3D paving of Spehner is equivalent to a tuple

      (D,α,β,γ)

  with

  * D a finite even set, whose elements are called darts;
  * α,β,γ fixed-point-free involutions on D.
  
  # Details

  We refer to “Merging in maps and in pavings” by Jean-Claude Spehner

  A Spehner paving is given (Definition 1.3) by ⟨D,α,σ,ϕ⟩ satisfying

  1. α involution without fixed-points
  2. ϕαϕ = α
  3. σϕ⁻¹σ = ϕ
  4. None of αϕ, ϕα, ϕσ⁻¹, ϕ⁻¹σ has a fixed point
  
  Letting β = αϕ and γ = σϕ⁻¹, we get:

  * β and γ have no fixed points
  * β² = αϕαϕ = α² = Id, γ² = σϕ⁻¹σϕ⁻¹ = ϕϕ⁻¹
  
  Hence we get a tuple (D,α,β,γ) as above. 
  From this tuple, we can recover ϕ and σ (satisfying conditions 1 till 4), so that we have the equivalence between tuples (D,α,σ,ϕ) and tuples (D,α,β,γ).

  # Dual Paving

  If a paving P= (D,α,σ,ϕ) is given, the underlying 2D map of P' = (D,ϕ⁻¹σ,σ⁻¹,σ⁻¹α) has as connected components the links of vertices of (D,α,σ,ϕ) (P' is the dual of P).
  Thus, to get the links of P, we just look at the connected components of (D,ϕ⁻¹σ,σ⁻¹), which, when using the (D,α,β,γ) representation, mean looking at the connected components of the 2D map (D,βαγαβ,βαγ).
  Up to isomorphism, this 2D-map is just (D,γ,γβα)

  # On the code

  In the code, we call this a /Spehner Map/ and if only the first two permutations α,β are given, a /Proto Spehner Map/.
  Two Spehner maps (D,α,β,γ) and (D',α',β',γ') are isomorphic if there exists a bijection f:D→D' such that α = f⁻¹◦α'◦f and similarly for β,γ.
  If two Spehner maps are isomorphic, in particular their underlying proto Spehner maps also are, and so are the tuples consisting of the first and third, and second and third permutations, respectively (i.e. all "submaps" of isomorphic maps are also isomorphic, obviously).

  A Spehner map can be seen as a trivalent graph on the set D of darts, with a three-coloring of the edges in such a way that each color  class forms a perfect matching.

  Under this interpretation, the underlying proto Spehner map is just a collection of even-length circuits with an “alternating” coloring of the edges.
  Once taken up to isomorphism, this is equivalent to a choice decomposition of the integer |D/2| as a sum of positive integers.
  For example, if there are 8 darts, we have

      4 = 1+1+1+1
        = 1+1+2
        = 1+3
        = 2+2

  which correspond to the proto Spehner maps consisting of, respectively: 4 two-cycles, 2 two-cycles plus 1 square, 1 two-cycle plus one hexagon, and 2 squares.

  Therefore, generating all  Spehner maps can be dealt with by looking at all extensions of a given proto-Spehner map (since extensions of non-isom proto-Spehner maps will be non-isom), and doing this for all proto-Spehner maps.

  The implementation below only deals with up to 24 darts.


*/

/// Given an even number of darts `number_darts`, returns the first permutation in a Spehner map, which we can choose, up to isom, to be the involution with cycle decomposition (0 n) (1 n-1) (2 n-2) etc
fn base_permutation(number_darts: usize) -> SubPermutation {
    SubPermutation::from(
        (0..number_darts as Dart)
            .map(|x| number_darts as Dart - x - 1)
            .collect::<Vec<Dart>>(),
    )
}

/// All the ways to write `total` (≥0) as a sum of of integers i≤`length_bound` (i≥1) up to
/// reordering.
/// Eg 4 = {1+1+1+1,1+1+2,1+3,2+2}.
fn partition_types(total: usize, length_bound: usize) -> Vec<Vec<usize>> {
    if total == 0 {
        vec![vec![]]
    } else {
        let min = total.min(length_bound);
        (1..min + 1)
            .map(|i| {
                partition_types(total - i, i).into_iter().map(move |mut v| {
                    v.push(i);
                    v
                })
            })
            .flatten()
            .collect()
    }
}

/// Builds a proto spehner map out of a partition type (see explanations at the top)
fn partition_type_to_proto_spehner_map(total: usize, mut partition_type: Vec<usize>) -> Map {
    let mut pointer = 0;

    let base = base_permutation(total * 2);
    let mut other: Vec<Dart> = (0..(total * 2) as Dart).collect();

    while let Some(length) = partition_type.pop() {
        for i in 0..length + 1 {
            let s = ((pointer + (i % length)) % total) as Dart;
            let t = (pointer + ((i + 1) % length)) % total;
            other[base.image(s) as usize] = t as Dart;
            other[t] = base.image(s);
        }
        pointer += length;
    }
    Map::from(vec![base, SubPermutation::from(other)])
}

/// Given a proto spehner map, returns the possible extensions (up to isomorphism) to Spehner maps.
fn extend_proto_spehner(m: &Map, number_darts: usize) -> Vec<Map> {
    
    // We want to keep track of time
    let now = SystemTime::now();
    eprintln!("START extensions of {}", m[1]);


    let full = bit_set_full_until_n(number_darts as Dart);
    let orbits_a = m[0].compute_orbits();
    let orbits_b = m[1].compute_orbits();

    // This is the orbit of the group ⟨α,β⟩
    let orbits_ab = join_partitions(&orbits_a, &orbits_b, &full);

    // For each orbit, we want to take as representative its least dart
    // orbit_rep maps a dart to its representative (initialized arbitrarily)
    let mut orbit_rep: DartArray = DartArray::identity();
    // orbit_card maps a dart to the size of its orbit (initialized arbitrarily)
    let mut orbit_card: DartArray = DartArray::from(vec![1 as Dart; DEGREE as usize]);
    // We now construct both orbit_rep and orbit_card
    for o in orbits_ab.clone() {
        let min_o = o.iter().min().unwrap();
        for d in o.iter() {
            orbit_rep.set_kv(d as Dart, min_o as Dart);
            orbit_card.set_kv(d as Dart, o.len() as Dart);
        }
    }
    

    // To construct an extension, we proceed naively:
    // We are given (D,α,β) and must construct γ.
    // So, we draw the edges corresponding to γ iteratively: 
    // We have a big list of partial γs, (partial matchings or partial permutations), initalized
    // with the empty matching
    // and we pick one such partial matching, find two free vertices, and connect them
    // If the result is a complete matching, we have found an extension, and add it to our list of
    // complete extensions, if it is not already there.
    //
    // We use two "tricks" to make that faster:
    // 1. Before testing for isomorphisms with the already present extensions, we first compare the
    //    partition types corresponding to the respective orbits of ⟨α,γ⟩ and ⟨β,γ⟩
    //    If the partition types are not equal, then obviously the maps are not isomorphic.
    //
    // 2. When building the extension γ, we keep a list of orbits of ⟨α,β⟩ which have no edge of γ
    //    incident to any of their vertices.
    //    Let C1 and C2 be two such "fresh" orbits of same cardinality: when adding a new edge, any
    //    choice of any vertex of C1 or C2 will yield isomorphic maps, so we may as well take the
    //    least dart of C1 and C2 combined.
    //    TODO: Actually, this could be improved by simply checking that our partial extension is
    //    not isomorphic, or isomorphic to an extension of an element of the partial extensions
    //    already present…
    //    That would mean modifying is_isomorphic() to check for being a "subgraph" up to
    //    isomorphism.
    //    Then, we would have one big heap of all extensions, complete or not, with no
    //    inclusion-up-to-isomomorphism relation between any of them.
    //    We then pop some element oout of the heap, try extending, and:
    //    * if it is a subgraph-up-to-isom, discard it
    //    * otherwise, discard all elements in the heap that are subgraphs-up-to-isom of our
    //    extension,and add our extension
    

    /// `o` represents a subset of a partition of the darts as follows:
    /// * if o.image(d) <= d, then o.image(d) is the representative of the part in which d lies,
    /// and this part is an element of the subset
    /// * if o.image(d) > d, then d lies in no part _in the subset_
    ///
    /// The function takes such a subset o, a dart d, and the array c assigning to each d the size
    /// of its partition, and returns true if either:
    /// * d is not in a part in the subset
    /// * d is in a part in the subset, and is least of all parts of same cardinalities as its
    /// parts
    fn is_first_in_fresh_orbits_ab(d: Dart, o: &DartArray, c: &DartArray) -> bool {
        //o.image(d) >= d
        if o.image(d) > d {
            return true;
        } else if o.image(d) == d {
            for d2 in 0..d {
                if o.image(d2) == d2 && c.image(d2) == c.image(d) {
                    return false;
                }
            }
            return true;
        } else {
            return false;
        }
    }
    
    /// removes the part corresponding to d (d is assumed to be the representative of its part)
    fn remove_dart_from_fresh_orbits_ab(d: Dart, o: &DartArray) -> DartArray {
        let mut o_bis = o.clone();
        for e in 0..DEGREE {
            if o_bis.image(e) == d {
                o_bis.set_kv(e, e + 1);
            }
        }
        o_bis
    }

    /// checks first that the partition types match and if so, test for isomorphism
    /// orbitxy are partition types, and orbita1 should be compared to orbita2 and orbitb1 to
    /// orbitb2
    fn check_isom(
        map1: &Map,
        orbita1: &Vec<Dart>,
        orbitb1: &Vec<Dart>,
        map2: &Map,
        orbita2: &Vec<Dart>,
        orbitb2: &Vec<Dart>,
    ) -> bool {
        if orbita1 != orbita2 || orbitb1 != orbitb2 {
            false
        } else {
            map1.is_isomorphic(map2)
        }
    }

    let empty_permutation: SubPermutation = SubPermutation::from((
        vec![],
        BitSet::with_capacity(DEGREE as usize),
        BitSet::with_capacity(DEGREE as usize),
    ));

    // Only one partial extension, with all orbits of ⟨α,β⟩ fresh
    let mut partial_extensions: Vec<(SubPermutation, DartArray)> =
        vec![(empty_permutation.clone(), orbit_rep.clone())];

    // No total extension (we store the partition types of ⟨α,γ⟩ and ⟨β,γ⟩ with our extensions)
    let mut total_extensions: Vec<(Map, Vec<Dart>, Vec<Dart>)> = Vec::new();

    while let Some((p, fresh_orbits_ab)) = partial_extensions.pop() {
        
        let free_darts = p.domain_complemented(&full);
        

        if let Some(source) = free_darts.iter().next() {
            if is_first_in_fresh_orbits_ab(source as Dart, &fresh_orbits_ab, &orbit_card) {
                
                let fresh_orbits_ab_minus_source =
                    remove_dart_from_fresh_orbits_ab(source as Dart, &fresh_orbits_ab);
                for target in free_darts.iter() {
                    if is_first_in_fresh_orbits_ab(
                        target as Dart,
                        &fresh_orbits_ab_minus_source,
                        &orbit_card,
                    ) && target != source
                    {
                        // If we're here, source is the first in a fresh orbit of a given cardinality
                        // (or in a non-fresh orbit) and target≠source is also first in a fresh
                        // orbit of a given cardinality (once the orbit of source is removed)
                        // So, we have a "useful" extension, and add it with fresh orbits
                        // recomputed

                        let mut p_extended = p.clone();
                        p_extended.set_kv(source as Dart, target as Dart);
                        p_extended.set_kv(target as Dart, source as Dart);

                        let fresh_orbits_ab_minus_source_and_target = remove_dart_from_fresh_orbits_ab(
                            target as Dart,
                            &fresh_orbits_ab_minus_source,
                        );

                        //println!("Adding {} and fresh orbits_ab are now {:?}", p_extended, fresh_orbits_ab_minus_source_and_target);
                        partial_extensions.push((p_extended, fresh_orbits_ab_minus_source_and_target));
                    }
                }
            }
        } else {

            // No free dart, so p is complete, and we want to add the map with γ := p to our list
            // of completed extensions

            let mut m1 = m.clone();
            m1.push(p.clone());


            let orbits_c = p.compute_orbits();

            // We compute the partition types of the orbits of ⟨α,γ⟩ and ⟨β,γ⟩ respectively
            let mut oa1: Vec<Dart> = join_partitions(
                &orbits_a,
                &orbits_c,
                &bit_set_full_until_n(number_darts as Dart),
            )
            .iter()
            .map(|x| x.len() as Dart)
            .collect();
            oa1.sort();
            let mut ob1: Vec<Dart> = join_partitions(
                &orbits_b,
                &orbits_c,
                &bit_set_full_until_n(number_darts as Dart),
            )
            .iter()
            .map(|x| x.len() as Dart)
            .collect();
            ob1.sort();
            
            // If our new completed map is connected, we add it if it is not isomorphic to some
            // already present map.
            if m1.is_connected()
                && total_extensions
                    .iter()
                    .all(|(m2, oa2, ob2)| !check_isom(&m1, &oa1, &ob1, m2, oa2, ob2))
            {
                total_extensions.push((m1, oa1, ob1));
            }
        }
    }

    eprintln!(
        "END   extensions of {} (after {} seconds)",
        m[1],
        now.elapsed().unwrap().as_secs()
    );

    //println!("<< extend {}",m[1].to_string());
    total_extensions.into_iter().map(|(m, _, _)| m).collect()
}

pub fn all_spehner_maps(number_darts: usize) -> Vec<Map> {
    eprintln!("all_spehner_maps({})", number_darts);

    // by proto_spehner I mean only the first two permutations (out of three)
    let all_proto_spehner: Vec<Map> = partition_types(number_darts / 2, number_darts / 2)
        .iter()
        .map(|x| partition_type_to_proto_spehner_map(number_darts / 2, x.clone()))
        .collect();

    //all_proto_spehner.par_iter().map(|m| extend_proto_spehner).flatten().collect()
    all_proto_spehner
        .par_iter()
        .map(|m| extend_proto_spehner(m, number_darts))
        .flatten()
        .collect()
}

pub fn print_all_spehner_maps(number_darts: usize) {
    
    eprintln!("all_spehner_maps({})", number_darts);
    let all_proto_spehner: Vec<Map> = partition_types(number_darts / 2, number_darts / 2)
        .iter()
        .map(|x| partition_type_to_proto_spehner_map(number_darts / 2, x.clone()))
        .collect();

    eprintln!("There are {} proto Spehner maps", all_proto_spehner.len());

    //all_proto_spehner.par_iter().map(|m| extend_proto_spehner).flatten().collect()
    let _: Vec<_> = all_proto_spehner
        .par_iter()
        .map(|m| {
            let m_extensions = extend_proto_spehner(m, number_darts);
            m_extensions.iter().for_each(|x| {
                let links_char = x.vertex_links_euler_char();
                let bdry_genera: Vec<_> = links_char
                    .iter()
                    .filter(|a| **a <= 0)
                    .map(|a| (2 - a) / 2)
                    .collect();
                println!("{} has boundary genera : {:?}", x, bdry_genera);
            })
        })
        .collect();
}

fn main() {
    let mut args: Vec<String> = env::args().collect();
    match args.pop().and_then(|x:String| x.parse::<usize>().ok()) {
        None => {
            eprintln!("I need an even number of darts between 2 and {}.", DEGREE);
            panic!();
        }    
        Some(n) => {
            if 2 <= n && n <= DEGREE as usize  && n % 2 == 0{
                print_all_spehner_maps(n);
            } else {
                eprintln!("I need an even number of darts between 2 and {}.", DEGREE);
                panic!();
            }
        }
    };

}

#[cfg(test)]
mod tests {
    use super::*;
    use darts_and_maps::map::*;

    #[test]
    fn test_Spehner_gmaps() {
        let known_values = vec![
            // The following ones correspond to Example 5.2 in Kolpakov&Ciobanu
            (4, 4),
            (6, 11),
            (8, 60),
            (10, 318),
            //(12,2806), // takes too long
        ];
        for (num_darts, num) in known_values.iter() {
            assert_eq!(
                all_spehner_maps(*num_darts).len() as usize,
                *num as usize,
                //format!("{} should yield {} but yielded {}", params, num, result)
            );
        }
    }

    #[test]
    fn connected_components_work() {
        for num_darts in (1..5).map(|x| 2 * x) {
            for link in all_spehner_maps(num_darts)
                .iter()
                .map(|m| m.link_of_spehner_map())
            {
                assert_eq!(
                    link.connected_components_domains().len(),
                    link.connected_components_maps().len()
                );
                assert_eq!(
                    link.connected_components_domains().len(),
                    link.orbits().len()
                );
            }
        }
    }

    #[test]
    fn euler_char_of_two_dim_maps() {
        assert!(true); //nice

        let two_darts_in_a_loop = Map::from(vec![
            SubPermutation::from(vec![1, 0]),
            SubPermutation::from(vec![1, 0]),
        ]);
        assert_eq!(two_darts_in_a_loop.two_dim_map_euler_char(), 2);

        let torus = Map::from(vec![
            SubPermutation::from(vec![1, 3, 0, 2]),
            SubPermutation::from(vec![3, 2, 1, 0]),
        ]);
        assert_eq!(torus.two_dim_map_euler_char(), 0);

        let three_edges_connecting_two_vertices = Map::from(vec![
            SubPermutation::from(vec![1, 2, 0, 4, 5, 3]),
            SubPermutation::from(vec![5, 4, 3, 2, 1, 0]),
        ]);
        assert_eq!(
            three_edges_connecting_two_vertices.two_dim_map_euler_char(),
            2
        );
    }

    #[test]
    fn links_of_Spehner_maps() {
        // TODO
        // Figure 8 knot complement as in Ciobanu&Kolpakov
    }
}
