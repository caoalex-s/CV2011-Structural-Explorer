import Std
import Std.Internal.Rat

abbrev Rat := Std.Internal.Rat

/-!
Exact polynomial certificates for the course beam methods.

Coefficients are rational, ordered from x^0 upwards. A six-coefficient vector
represents a polynomial of degree at most five. The generator checks degree
bounds before using these operations. No sampled or floating-point equality
is used. D and primitive are the formal polynomial derivative and primitive.
This library does not axiomatise real calculus or prove the mechanical laws.
Each generated theorem checks the stated algebraic consequences of those laws.
-/
namespace BeamCertificate

abbrev Poly := List Rat

def coefficient (p : Poly) (i : Nat) : Rat := p[i]?.getD 0
def polynomial (f : Nat → Rat) : Poly := (List.range 6).map f
def constant (a : Rat) : Poly := polynomial fun i => if i == 0 then a else 0
def add (p q : Poly) : Poly := polynomial fun i => coefficient p i + coefficient q i
def scale (a : Rat) (p : Poly) : Poly := polynomial fun i => a * coefficient p i
def multiply (p q : Poly) : Poly := polynomial fun i =>
  ((List.range (i + 1)).map fun j => coefficient p j * coefficient q (i - j)).sum
def value (p : Poly) (x : Rat) : Rat := p.foldr (fun a v => a + x * v) 0
def D (p : Poly) : Poly := polynomial fun i =>
  Std.Internal.mkRat (Int.ofNat (i + 1)) 1 * coefficient p (i + 1)
def primitive (p : Poly) : Poly := polynomial fun i =>
  if i == 0 then 0 else coefficient p (i - 1) / Std.Internal.mkRat (Int.ofNat i) 1
def integral (p : Poly) (a b : Rat) : Rat := value (primitive p) b - value (primitive p) a

structure Action where
  x : Rat
  fx : Rat
  fy : Rat
  couple : Rat

structure Distributed where
  start : Rat
  finish : Rat
  q0 : Rat
  q1 : Rat

def intensity (load : Distributed) : Poly :=
  let slope := (load.q1 - load.q0) / (load.finish - load.start)
  [load.q0 - slope * load.start, slope, 0, 0, 0, 0]

def distributedV (load : Distributed) (cut : Rat) : Poly :=
  if cut ≤ load.start then constant 0 else
  if cut ≥ load.finish then constant (integral (intensity load) load.start load.finish) else
  add (primitive (intensity load)) (constant (-value (primitive (intensity load)) load.start))

def distributedM (load : Distributed) (cut : Rat) : Poly :=
  let q := intensity load
  let xq := multiply [0, 1, 0, 0, 0, 0] q
  let firstMoment := if cut ≤ load.start then constant 0 else
    if cut ≥ load.finish then constant (integral xq load.start load.finish) else
    add (primitive xq) (constant (-value (primitive xq) load.start))
  add (multiply [0, 1, 0, 0, 0, 0] (distributedV load cut)) (scale (-1) firstMoment)

def sumPolys (ps : List Poly) : Poly := ps.foldl add (constant 0)
def cutN (actions : List Action) (cut : Rat) : Poly :=
  constant (((actions.filter fun a => a.x < cut).map fun a => -a.fx).sum)
def cutV (actions : List Action) (loads : List Distributed) (cut : Rat) : Poly :=
  add (constant (((actions.filter fun a => a.x < cut).map fun a => a.fy).sum))
    (sumPolys (loads.map fun load => distributedV load cut))
def cutM (actions : List Action) (loads : List Distributed) (cut : Rat) : Poly :=
  add (sumPolys ((actions.filter fun a => a.x < cut).map fun a =>
    [-a.fy * a.x - a.couple, a.fy, 0, 0, 0, 0]))
    (sumPolys (loads.map fun load => distributedM load cut))
def cutQ (loads : List Distributed) (cut : Rat) : Poly :=
  sumPolys ((loads.filter fun load => load.start < cut && cut < load.finish).map intensity)

/- Range certificates use t=(x-a)/(b-a) on each covered interval.
The six basis polynomials are choose(5,i)*t^i*(1-t)^(5-i).
They are nonnegative for 0 <= t <= 1 and sum to one. Generated
statements check the exact basis conversion and every coefficient bound.
The real-domain convex-hull interpretation is stated in the proof scope. -/
def bernsteinBasis : List Poly := [
  [1, -5, 10, -10, 5, -1], [0, 5, -20, 30, -20, 5],
  [0, 0, 10, -30, 30, -10], [0, 0, 0, 10, -20, 10],
  [0, 0, 0, 0, 5, -5], [0, 0, 0, 0, 0, 1]]

def bernstein5 (weights : List Rat) : Poly :=
  sumPolys ((List.range 6).map fun i =>
    scale (coefficient weights i) (bernsteinBasis[i]?.getD []))

def affineCompose (p : Poly) (a b : Rat) : Poly :=
  p.foldr (fun c rest => add (constant c) (multiply [a, b-a, 0, 0, 0, 0] rest)) (constant 0)

theorem bernstein_partition_of_unity : sumPolys bernsteinBasis = constant 1 := by decide

end BeamCertificate
