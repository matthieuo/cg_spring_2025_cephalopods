use std::io;
use itertools::Itertools;
use std::collections::HashMap;

use rustc_hash::FxBuildHasher; // not available in codingame, can be copy pasted from https://github.com/rust-lang/rustc-hash, I put here for clarity


macro_rules! parse_input {
    ($x:expr, $t:ident) => ($x.trim().parse::<$t>().unwrap())
}

const BITS_PER_CELL: usize = 3;
const CELL_MASK: u32 = 0x7; // 111 in binary

// Precalculated table for neighbors of each position
//  [pos] -> [neighbor1, neighbor2, neighbor3, neighbor4] (-1 = invalid positions)
const NEIGHBOR_POSITIONS: [[(i32, i32); 4]; 9] = [
    [(0, 1), (1, 0), (-1, -1), (-1, -1)], // (0,0)
    [(0, 0), (0, 2), (1, 1), (-1, -1)],   // (0,1)
    [(0, 1), (1, 2), (-1, -1), (-1, -1)], // (0,2)
    [(0, 0), (1, 1), (2, 0), (-1, -1)],   // (1,0)
    [(0, 1), (1, 2), (2, 1), (1, 0)],     // (1,1)
    [(0, 2), (1, 1), (2, 2), (-1, -1)],   // (1,2)
    [(1, 0), (2, 1), (-1, -1), (-1, -1)], // (2,0)
    [(1, 1), (2, 0), (2, 2), (-1, -1)],   // (2,1)
    [(1, 2), (2, 1), (-1, -1), (-1, -1)], // (2,2)
];





#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
struct Board {
    data: u32
}



impl Board {
    fn new() -> Self {
        Board { data: 0 }
    }
    
    fn from_vec(v: &[i32]) -> Self {
        let mut board = Board::new();
        for (idx, &val) in v.iter().enumerate() {
            board.set(idx / 3, idx % 3, val as u8);
        }
        board
    }
    
     #[inline]
    fn get(&self, row: usize, col: usize) -> u8 {
        let pos = row * 3 + col;
        ((self.data >> ((pos * BITS_PER_CELL) as u32)) & CELL_MASK) as u8
    }
    
 
    #[inline]
    fn set(&mut self, row: usize, col: usize, value: u8) {
        let pos = row * 3 + col;
        let shift = pos * BITS_PER_CELL;
        // Clear old value
        self.data &= !(CELL_MASK << (shift as u32));
	self.data |= (value as u32) << (shift as u32);
    }
    
    #[inline]  
    fn to_int(&self) -> u32 {
    
        const POWERS: [u32; 9] = [
            100000000, 10000000, 1000000, 100000, 10000, 1000, 100, 10, 1
        ];
        
        // Manual loop unrolling (usefull ????)
        (self.get(0, 0) as u32) * POWERS[0] +
            (self.get(0, 1) as u32) * POWERS[1] +
            (self.get(0, 2) as u32) * POWERS[2] +
            (self.get(1, 0) as u32) * POWERS[3] +
            (self.get(1, 1) as u32) * POWERS[4] +
            (self.get(1, 2) as u32) * POWERS[5] +
            (self.get(2, 0) as u32) * POWERS[6] +
            (self.get(2, 1) as u32) * POWERS[7] +
            (self.get(2, 2) as u32) * POWERS[8]
    }
    
    #[inline]
    fn is_full(&self) -> bool {
        let bit_mask = 0x1_24_92_49;  // 1 in the lowest bit of each bit triple (positions 0,3,6,9,12,15,18,21,24)
        let all_cells_check = (self.data | (self.data >> 1) | (self.data >> 2)) & bit_mask;
        
        all_cells_check == bit_mask
    }
    #[inline]
    fn cells(&self) -> impl Iterator<Item = (usize, usize)> {
        (0..3).cartesian_product(0..3)
    }
    
    #[inline]
    fn empty_cells(&self) -> impl Iterator<Item = (usize, usize)> + '_ {
        self.cells().filter(move |(row, col)| self.get(*row, *col) == 0)
    }
    
 
 
//#[inline(never)]
fn generate_next_states<F>(&self, mut callback: F)
where
    F: FnMut(Board)
{
    //  board is full 
    if self.is_full() {
        return;
    }
    
    // Pre-computed bit shifts for each position to avoid repeated calculations
    const CELL_SHIFTS: [u32; 9] = [0, 3, 6, 9, 12, 15, 18, 21, 24];
    
    // Iterate through all positions directly rather than row/col conversion
    for pos in 0..9 {
        let shift = CELL_SHIFTS[pos];
        
        // Fast check if cell is occupied using bit operations
        if ((self.data >> shift) & CELL_MASK) != 0 {
            continue;
        }
        
        // Get neighbors efficiently
        let mut neighbors = [(0u32, 0u8); 4]; // Store shift position and value
        let mut neighbor_count = 0;
        
        // Use pre-computed neighbor positions
        for &(nr, nc) in &NEIGHBOR_POSITIONS[pos] {
            if nr >= 0 && nc >= 0 {
                let npos = (nr as usize) * 3 + (nc as usize);
                let nshift = CELL_SHIFTS[npos];
                let nvalue = ((self.data >> nshift) & CELL_MASK) as u8;
                
                if nvalue > 0 {
                    neighbors[neighbor_count] = (nshift, nvalue);
                    neighbor_count += 1;
                }
            }
        }
        
        // Fast path for no/single neighbor (no capture possible)
        if neighbor_count < 2 {
            // Create new board with a '1' at current position using direct bit operations
            callback(Board { data: self.data | (1 << shift) });
            continue;
        }
        
        let mut capture_found = false;
        
   
        match neighbor_count {
            2 => {
                // Only one possible capture combination with 2 neighbors
                let sum = neighbors[0].1 + neighbors[1].1;
                
                if sum <= 6 {
                    capture_found = true;
                    
                    // Fast bit manipulation for board creation
                    let mut new_data = self.data;
                    // Clear neighbors
                    new_data &= !(CELL_MASK << neighbors[0].0);
                    new_data &= !(CELL_MASK << neighbors[1].0);
                    // Set new value
                    new_data |= (sum as u32) << shift;
                    
                    callback(Board { data: new_data });
                }
            },
            3 => {
                // Check all pairs (3 combinations)
                for i in 0..3 {
                    for j in i+1..3 {
                        let sum = neighbors[i].1 + neighbors[j].1;
                        
                        if sum <= 6 {
                            capture_found = true;
                            
                            let mut new_data = self.data;
                            new_data &= !(CELL_MASK << neighbors[i].0);
                            new_data &= !(CELL_MASK << neighbors[j].0);
                            new_data |= (sum as u32) << shift;
                            
                            callback(Board { data: new_data });
                        }
                    }
                }
                
                // Check the triplet
                let sum = neighbors[0].1 + neighbors[1].1 + neighbors[2].1;
                
                if sum <= 6 {
                    capture_found = true;
                    
                    let mut new_data = self.data;
                    new_data &= !(CELL_MASK << neighbors[0].0);
                    new_data &= !(CELL_MASK << neighbors[1].0);
                    new_data &= !(CELL_MASK << neighbors[2].0);
                    new_data |= (sum as u32) << shift;
                    
                    callback(Board { data: new_data });
                }
            },
            4 => {
                    
                // All 6 combinations
                for i in 0..4 {
                    for j in i+1..4 {
                        let sum = neighbors[i].1 + neighbors[j].1;
                        
                        if sum <= 6 {
                            capture_found = true;
                            
                            let mut new_data = self.data;
                            new_data &= !(CELL_MASK << neighbors[i].0);
                            new_data &= !(CELL_MASK << neighbors[j].0);
                            new_data |= (sum as u32) << shift;
                            
                            callback(Board { data: new_data });
                        }
                    }
                }
                
                // All 4 combinations
                for i in 0..4 {
                    for j in i+1..4 {
                        for k in j+1..4 {
                            let sum = neighbors[i].1 + neighbors[j].1 + neighbors[k].1;
                            
                            if sum <= 6 {
                                capture_found = true;
                                
                                let mut new_data = self.data;
                                new_data &= !(CELL_MASK << neighbors[i].0);
                                new_data &= !(CELL_MASK << neighbors[j].0);
                                new_data &= !(CELL_MASK << neighbors[k].0);
                                new_data |= (sum as u32) << shift;
                                
                                callback(Board { data: new_data });
                            }
                        }
                    }
                }
                
                // 4
                let sum = neighbors[0].1 + neighbors[1].1 + neighbors[2].1 + neighbors[3].1;
                
                if sum <= 6 {
                    capture_found = true;
                    
                    let mut new_data = self.data;
                    new_data &= !(CELL_MASK << neighbors[0].0);
                    new_data &= !(CELL_MASK << neighbors[1].0);
                    new_data &= !(CELL_MASK << neighbors[2].0);
                    new_data &= !(CELL_MASK << neighbors[3].0);
                    new_data |= (sum as u32) << shift;
                    
                    callback(Board { data: new_data });
                }
            },
            _ => unreachable!()
        }
        
        // If no capture was possible, place a die with value 1
        if !capture_found {
            callback(Board { data: self.data | (1 << shift) });
        }
    }
}


//#[inline(never)]
fn transform_vec(&self) -> [Board; 8] {
    let mut result = [Board::new(); 8];
    
    // Set identity transformation
    result[0] = *self;
    
    // Transformation 1: 90° clockwise rotation
    for r in 0..3 {
        for c in 0..3 {
            result[1].set(c, 2-r, self.get(r, c));
        }
    }
    
    // Transformation 2: 180° rotation
    for r in 0..3 {
        for c in 0..3 {
            result[2].set(2-r, 2-c, self.get(r, c));
        }
    }
    
    // Transformation 3: 270° clockwise rotation
    for r in 0..3 {
        for c in 0..3 {
            result[3].set(2-c, r, self.get(r, c));
        }
    }
    
    // Transformation 4: Horizontal reflection
    for r in 0..3 {
        for c in 0..3 {
            result[4].set(r, 2-c, self.get(r, c));
        }
    }
    
    // Transformation 5: Vertical reflection
    for r in 0..3 {
        for c in 0..3 {
            result[5].set(2-r, c, self.get(r, c));
        }
    }
    
    // Transformation 6: Main diagonal reflection
    for r in 0..3 {
        for c in 0..3 {
            result[6].set(c, r, self.get(r, c));
        }
    }
    
    // Transformation 7: Anti-diagonal reflection
    for r in 0..3 {
        for c in 0..3 {
            result[7].set(2-c, 2-r, self.get(r, c));
        }
    }
    
    result
}
    
//#[inline(never)]
fn transform(&self, transformation: u8) -> Board {
    // Fast path for identity transform
    if transformation == 0 {
        return *self;
    }
    
    let mut result = Board::new();
    
    // Transformation mappings that match the test expectations
    match transformation {
        0 => return *self, // Identity
        
        1 => { // 90° clockwise
            for row in 0..3 {
                for col in 0..3 {
                    // (r,c) -> (c,2-r)
                    result.set(col, 2-row, self.get(row, col));
                }
            }
        },
        
        2 => { // 180°
            for row in 0..3 {
                for col in 0..3 {
                    // (r,c) -> (2-r,2-c)
                    result.set(2-row, 2-col, self.get(row, col));
                }
            }
        },
        
        3 => { // 270° clockwise
            for row in 0..3 {
                for col in 0..3 {
                    // (r,c) -> (2-c,r)
                    result.set(2-col, row, self.get(row, col));
                }
            }
        },
        
        4 => { // Horizontal reflection
            for row in 0..3 {
                for col in 0..3 {
                    // (r,c) -> (r,2-c)
                    result.set(row, 2-col, self.get(row, col));
                }
            }
        },
        
        5 => { // Vertical reflection
            for row in 0..3 {
                for col in 0..3 {
                    // (r,c) -> (2-r,c)
                    result.set(2-row, col, self.get(row, col));
                }
            }
        },
        
        6 => { // Main diagonal reflection
            for row in 0..3 {
                for col in 0..3 {
                    // (r,c) -> (c,r)
                    result.set(col, row, self.get(row, col));
                }
            }
        },
        
        7 => { // Anti-diagonal reflection
            for row in 0..3 {
                for col in 0..3 {
                    // (r,c) -> (2-c,2-r)
                    result.set(2-col, 2-row, self.get(row, col));
                }
            }
        },
        
        _ => panic!("Invalid transformation"),
    }
    
    result
}

    //#[inline]

 //   #[inline(never)]
fn canonical_form(&self) -> (Board, u8) {

    if self.data == 0 {
        return (*self, 0);
    }
    


    let transforms = self.transform_vec(); //vec version

    
 
    let mut min_idx = 0;
    let mut min_data = transforms[0].data;
    
  
    for i in 1..8 {
        if transforms[i].data < min_data {
            min_data = transforms[i].data;
            min_idx = i;
        }
    }
    
    (transforms[min_idx], min_idx as u8)
}
}


//#[inline]
fn inverse_transform(transform_idx: u8) -> u8 {
    match transform_idx {
        0 => 0, // Identity
        1 => 3, // Rotation 90° -> Rotation 270°
        2 => 2, // Rotation 180° -> Rotation 180°
        3 => 1, // Rotation 270° -> Rotation 90°
        4 => 4, // Horizontal reflection -> Horizontal reflection
        5 => 5, // Vertical reflection -> Vertical reflection
        6 => 6, // Main diagonal reflection -> Main diagonal reflection
        7 => 7, // Other diagonal reflection -> Other diagonal reflection
        _ => panic!("Invalid transformation")
    }
}
fn simulate_games(initial_board: Board, max_depth: i32) -> u32 {
   
    let mut current_states: HashMap<Board, [u32; 8], FxBuildHasher> = 
        HashMap::with_capacity_and_hasher(1_000, FxBuildHasher);
    let mut next_states: HashMap<Board, [u32; 8], FxBuildHasher> = 
        HashMap::with_capacity_and_hasher(1_000, FxBuildHasher);
    
    // Precompute transformation composition table
    let compose = precompute_transformation_composition();

    // Get canonical form of initial board
    let (canonical, transform_idx) = initial_board.canonical_form();
    
    // The transformation to go from canonical back to original is the inverse
    let initial_inverse_idx = inverse_transform(transform_idx);
    
    // Set up initial state with count 1 for the appropriate transformation
    let mut initial_counts = [0; 8];
    initial_counts[initial_inverse_idx as usize] = 1;
    
    current_states.insert(canonical, initial_counts);
    
    // use vector, seems to reduce cache misses
    let mut next_boards = Vec::with_capacity(16);
    let mut next_transforms = Vec::with_capacity(16);
    
    // Process each turn
    for _ in 0..max_depth {
        //next_states.clear();
        
        for (canonical_board, transform_counts) in current_states.drain() {
            if canonical_board.is_full() {
                // Full board - preserve as is
                let entry = next_states.entry(canonical_board).or_insert([0; 8]);
		//entry.copy_from_slice(&transform_counts);
                for i in 0..8 {
                    entry[i] += transform_counts[i];
                }
                continue;
            }
            
          
            next_boards.clear();
            next_transforms.clear();
            
            
            canonical_board.generate_next_states(|next_board| {
                let (next_canonical, trans) = next_board.canonical_form();
                next_boards.push(next_canonical);
                next_transforms.push(trans);
            });
            
        
            for (move_idx, next_canonical) in next_boards.iter().enumerate() {
                let next_trans = next_transforms[move_idx];
                let next_inverse = inverse_transform(next_trans);
                
          
                let entry = next_states.entry(*next_canonical).or_insert([0; 8]);
                
       
                for orig_trans in 0..8 {
                    let count = transform_counts[orig_trans];
                    let composed_trans = compose[orig_trans][next_inverse as usize];
                    entry[composed_trans] += count;
                }
                
            }
        }
        
        std::mem::swap(&mut current_states, &mut next_states);
    }
    
  
    let mut final_sum = 0;
    for (canonical_board, transform_counts) in current_states {
        for i in 0..8 {
            let count = transform_counts[i];
            if count > 0 {
                let transformed = canonical_board.transform(i as u8);
                let hash = transformed.to_int();
                final_sum = (final_sum + hash.wrapping_mul(count)) % (1 << 30); 
            }
            
        }
    }

    final_sum
}


// Precompute the composition of transformations
fn precompute_transformation_composition() -> [[usize; 8]; 8] {
    let mut compose = [[0; 8]; 8];
    
    // For each combination of transformations i and j
    for i in 0..8 {
        for j in 0..8 {
            // Create a test board 
            let mut test_board = Board::new();
            test_board.set(0, 0, 1);
            test_board.set(0, 1, 2);
            test_board.set(1, 0, 3);
            
            // Apply  j then i
            let board_j = test_board.transform(j as u8);
            let board_ij = board_j.transform(i as u8);
            
            // Find which  transformation gives the same result
            for k in 0..8 {
                if test_board.transform(k as u8).data == board_ij.data {
                    compose[i][j] = k;
                    break;
                }
            }
        }
    }
    
    compose
}



fn main() {
    let mut input_line = String::new();
    let mut v_board_flat = Vec::<i32>::new();
    io::stdin().read_line(&mut input_line).unwrap();
    let depth = parse_input!(input_line, i32);
    
    for _ in 0..3 {
        let mut inputs = String::new();
        io::stdin().read_line(&mut inputs).unwrap();
        for j in inputs.split_whitespace() {
            let value = parse_input!(j, i32);
            v_board_flat.push(value);
        }
    }



    let initial_board = Board::from_vec(&v_board_flat);
    
    let final_sum = simulate_games(initial_board, depth);
    
    println!("{}", final_sum);
}


