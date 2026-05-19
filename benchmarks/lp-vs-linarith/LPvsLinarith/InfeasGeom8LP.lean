import Soplex
import Mathlib.Tactic.Linarith
set_option maxHeartbeats 4000000
example (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Rat) (_p0 : 0 ≤ x0) (_p1 : 0 ≤ x1) (_p2 : 0 ≤ x2) (_p3 : 0 ≤ x3) (_p4 : 0 ≤ x4) (_p5 : 0 ≤ x5) (_p6 : 0 ≤ x6) (_p7 : 0 ≤ x7) (_p8 : 0 ≤ x8) (_h0 : x0 ≤ 1) (_h1 : 3 * x1 ≤ 2 * x0) (_h2 : 3 * x2 ≤ 2 * x1) (_h3 : 3 * x3 ≤ 2 * x2) (_h4 : 3 * x4 ≤ 2 * x3) (_h5 : 3 * x5 ≤ 2 * x4) (_h6 : 3 * x6 ≤ 2 * x5) (_h7 : 3 * x7 ≤ 2 * x6) (_h8 : 3 * x8 ≤ 2 * x7) (_hC : 257 ≤ 6561 * x8) :
    x0 ≤ -1 := by lp
