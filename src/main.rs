use std::collections::{HashMap, VecDeque};
use std::fmt;

/// A Permutation struct acting on points 0..N-1
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Permutation {
    map: Vec<usize>,
}

impl Permutation {
    pub fn new(map: Vec<usize>) -> Self {
        // Validate that it is a proper permutation
        let n = map.len();
        let mut seen = vec![false; n];
        for &x in &map {
            if x >= n || seen[x] {
                panic!("Invalid permutation vector");
            }
            seen[x] = true;
        }
        Permutation { map }
    }

    pub fn identity(n: usize) -> Self {
        Permutation {
            map: (0..n).collect(),
        }
    }

    /// Apply the permutation to a point
    pub fn apply(&self, point: usize) -> usize {
        self.map[point]
    }

    /// Composition: (self * other)(x) = self(other(x))
    /// Note: Typical group theory notation goes right-to-left, 
    ///       but code often executes left-to-right. 
    ///       Here we implement: result[i] = self[other[i]]
    pub fn multiply(&self, other: &Permutation) -> Self {
        let n = self.map.len();
        assert_eq!(n, other.map.len());
        let map = (0..n).map(|i| self.apply(other.apply(i))).collect();
        Permutation { map }
    }

    /// Inverse of the permutation
    pub fn inverse(&self) -> Self {
        let n = self.map.len();
        let mut inv = vec![0; n];
        for (i, &val) in self.map.iter().enumerate() {
            inv[val] = i;
        }
        Permutation { map: inv }
    }
    
    pub fn is_identity(&self) -> bool {
        self.map.iter().enumerate().all(|(i, &x)| i == x)
    }
}

impl fmt::Debug for Permutation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.map)
    }
}

/// Represents a level in the Stabilizer Chain
struct StabilizerLevel {
    base_point: usize,
    /// Generators for this specific stabilizer level
    generators: Vec<Permutation>,
    /// The Orbit of the base_point under these generators
    /// Maps: point_in_orbit -> transversal_element
    ///       transversal_element maps base_point -> point_in_orbit
    transversal: HashMap<usize, Permutation>,
}

impl StabilizerLevel {
    fn new(base_point: usize, n: usize) -> Self {
        let id = Permutation::identity(n);
        let mut transversal = HashMap::new();
        transversal.insert(base_point, id);
        
        StabilizerLevel {
            base_point,
            generators: Vec::new(),
            transversal,
        }
    }
}

pub struct SchreierSims {
    n: usize,
    chain: Vec<StabilizerLevel>,
}

impl SchreierSims {
    pub fn new(n: usize) -> Self {
        SchreierSims {
            n,
            chain: Vec::new(),
        }
    }

    /// Main entry point: Add a generator to the group.
    /// This updates the BSGS to include the new element.
    pub fn add_generator(&mut self, p: Permutation) {
        assert_eq!(p.map.len(), self.n);
        self.insert(p, 0);
    }

    /// Recursive insertion (The "Filter" or "Strip" process)
    fn insert(&mut self, h: Permutation, level: usize) {
        if h.is_identity() {
            return;
        }

        // If we have run out of levels but h is not identity,
        // we must extend the base.
        if level >= self.chain.len() {
            // Pick the first point moved by h as the new base point
            let new_base = h.map.iter()
                .enumerate()
                .find(|&(i, &x)| i != x)
                .map(|(i, _)| i)
                .unwrap();

            self.chain.push(StabilizerLevel::new(new_base, self.n));
        }

        let current_level = &mut self.chain[level];
        let base = current_level.base_point;
        let image = h.apply(base);

        // 1. Check if the image is already in the orbit (Transversal check)
        if let Some(transversal_element) = current_level.transversal.get(&image) {
            // Known orbit point: Strip this level off h and recurse
            // h_new = u^-1 * h, where u maps base -> image
            let u_inv = transversal_element.inverse();
            let h_next = u_inv.multiply(&h);
            
            // h_next now fixes the current base point, push it deeper
            self.insert(h_next, level + 1);
        } else {
            // 2. New orbit point found implies h is a new strong generator
            current_level.generators.push(h.clone());
            
            // We must update the orbit (transversal) at this level
            // This is the most computationally intensive part.
            // Any new transversal element might create new Schreier generators 
            // deeper in the chain.
            self.update_orbit(level);
        }
    }

    /// Perform a BFS to update the orbit/transversal at a specific level
    /// using the newly added generator.
    fn update_orbit(&mut self, level: usize) {
        // We use an index-based loop because we need to borrow self mutably 
        // to call `insert`, but we need to read from `chain[level]`.
        
        let mut queue = VecDeque::new();
        
        // In an optimised version, we wouldn't rebuild the whole orbit,
        // but for clarity / simplicity, we ensure consistency by processing
        // new edges in the Schreier graph.
        
        // Populate queue with existing orbit points
        for &pt in self.chain[level].transversal.keys() {
            queue.push_back(pt);
        }

        // We specifically look for applications of generators that reach NEW points
        // or new generators on OLD points. 
        // A simplified logic: Run BFS until no new points are found.
        
        // Note: In a production 'incremental' implementation, you carefully 
        //       track "new" generators vs "old" orbit points to avoid redundant work.
        //       Here, we just rely on the transversal check to stop cycles.

        let mut ptr = 0;
        // Snapshot the generators indices to avoid borrow checker issues
        let gen_count = self.chain[level].generators.len();

        // Standard BFS for orbit
        while ptr < queue.len() {
            let u_pt = queue[ptr];
            ptr += 1;

            // We need the transversal element for u (u_perm maps base -> u)
            // Clone it to release the borrow on self.chain
            let u_perm = self.chain[level].transversal[&u_pt].clone();

            for i in 0..gen_count {
                let s_perm = self.chain[level].generators[i].clone();
                
                // New point v = s(u)
                let v_pt = s_perm.apply(u_pt);

                if !self.chain[level].transversal.contains_key(&v_pt) {
                    // Found a new point in orbit!
                    // The transversal element is s * u
                    let new_transversal = s_perm.multiply(&u_perm);
                    self.chain[level].transversal.insert(v_pt, new_transversal.clone());
                    queue.push_back(v_pt);
                    
                    // IMPORTANT: Schreier Generator check is implicitly handled 
                    // because next time we `insert` something that lands on `v_pt`,
                    // it will be sifted using `new_transversal`.
                } else {
                    // This is the "Schreier Generator" step.
                    // We found a cycle: s maps u -> v, and we already visited v.
                    // The element (transversal[v])^-1 * s * transversal[u] is in the stabilizer.
                    // We must sift this element to ensuring the next levels are correct.
                    
                    let v_rep = &self.chain[level].transversal[&v_pt];
                    // schreier_gen = v_rep^-1 * s * u_rep
                    // This element maps base -> u -> v -> base (stabilizes base)
                    let schreier_gen = v_rep.inverse()
                        .multiply(&s_perm)
                        .multiply(&u_perm);
                    
                    // Recursively ensure this stabilizer is in the lower chain
                    self.insert(schreier_gen, level + 1);
                }
            }
        }
    }

    /// Calculates the order of the group |G|
    /// |G| = product of orbit sizes at each level
    pub fn order(&self) -> u128 {
        self.chain.iter().map(|level| level.transversal.len() as u128).product()
    }
    
    /// Checks if a permutation is a member of the group
    pub fn contains(&self, mut g: Permutation) -> bool {
        for level in &self.chain {
            let base = level.base_point;
            let image = g.apply(base);
            
            if let Some(transversal_elem) = level.transversal.get(&image) {
                // Strip: g = u^-1 * g
                let u_inv = transversal_elem.inverse();
                g = u_inv.multiply(&g);
            } else {
                return false;
            }
        }
        g.is_identity()
    }
}

fn main() {
    // Example: The Symmetric Group S4 (Permutations of 0,1,2,3)
    // Generated by s1=(0 1) and s2=(0 1 2 3)
    
    // (0 1)
    let s1 = Permutation::new(vec![1, 0, 2, 3]);
    // (0 1 2 3) -> 0->1, 1->2, 2->3, 3->0
    let s2 = Permutation::new(vec![1, 2, 3, 0]);

    let mut algo = SchreierSims::new(4);
    
    println!("Adding generator s1: {:?}", s1);
    algo.add_generator(s1);
    
    println!("Adding generator s2: {:?}", s2);
    algo.add_generator(s2);

    println!("---");
    println!("Calculated Group Order: {}", algo.order());
    println!("Expected Order for S4: 24");
    println!("Base points chosen: {:?}", algo.chain.iter().map(|l| l.base_point).collect::<Vec<_>>());

    // Membership tests
    let p_in = Permutation::new(vec![3, 2, 1, 0]); // Reversal, should be in S4
    let p_out_len = Permutation::new(vec![0, 1, 2, 3]); // Identity is in
    
    println!("Contains reversal (3,2,1,0)? {}", algo.contains(p_in));
    println!("Contains identity? {}", algo.contains(p_out_len));

    // Construct a permutation not in S4? (Impossible for N=4 as S4 is all perms)
    // Let's try S3 embedded in 4 points (fixing 3)
    println!("\n--- Test S3 (fixing index 3) ---");
    let mut s3_algo = SchreierSims::new(4);
    let s3_gen1 = Permutation::new(vec![1, 0, 2, 3]); // (0 1)
    let s3_gen2 = Permutation::new(vec![1, 2, 0, 3]); // (0 1 2)
    s3_algo.add_generator(s3_gen1);
    s3_algo.add_generator(s3_gen2);
    
    println!("Order of S3: {}", s3_algo.order());
    let bad_perm = Permutation::new(vec![0, 1, 3, 2]); // Swaps 2 and 3
    println!("Contains swap(2,3)? {}", s3_algo.contains(bad_perm)); // Should be false
}
