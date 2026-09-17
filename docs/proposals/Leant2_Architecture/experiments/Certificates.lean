import Mathlib
namespace Leant2Affine

def affine (c a b d : Nat) : List Nat → Nat
  | [] => c
  | x :: xs => a * x + b * affine c a b d xs + d

/-- Inductive summary certificate for a whole (unbounded) family of lists. -/
theorem certify {c a b d A B C : Nat}
    (h0 : c = C) (ha : a = A) (hba : b * A = A) (hbb : b * B = B)
    (hc : b * C + d = B + C) :
    ∀ xs : List Nat, affine c a b d xs = A * xs.sum + B * xs.length + C := by
  subst a
  intro xs
  induction xs with
  | nil => simp [affine, h0]
  | cons x xs ih =>
    simp only [affine, ih, List.sum_cons, List.length_cons,
      Nat.mul_add, ← Nat.mul_assoc, hba, hbb, Nat.mul_one]
    omega

#print axioms certify

theorem task_000 : ∀ xs : List Nat,
    affine 0 0 0 0 xs = 0 * xs.sum + 0 * xs.length + 0 := by
  apply certify <;> decide
#print axioms task_000

theorem task_001 : ∀ xs : List Nat,
    affine 1 0 0 1 xs = 0 * xs.sum + 0 * xs.length + 1 := by
  apply certify <;> decide
#print axioms task_001

theorem task_002 : ∀ xs : List Nat,
    affine 2 0 1 0 xs = 0 * xs.sum + 0 * xs.length + 2 := by
  apply certify <;> decide
#print axioms task_002

theorem task_003 : ∀ xs : List Nat,
    affine 0 0 1 1 xs = 0 * xs.sum + 1 * xs.length + 0 := by
  apply certify <;> decide
#print axioms task_003

theorem task_004 : ∀ xs : List Nat,
    affine 1 0 1 1 xs = 0 * xs.sum + 1 * xs.length + 1 := by
  apply certify <;> decide
#print axioms task_004

theorem task_005 : ∀ xs : List Nat,
    affine 2 0 1 1 xs = 0 * xs.sum + 1 * xs.length + 2 := by
  apply certify <;> decide
#print axioms task_005

theorem task_006 : ∀ xs : List Nat,
    affine 0 0 1 2 xs = 0 * xs.sum + 2 * xs.length + 0 := by
  apply certify <;> decide
#print axioms task_006

theorem task_007 : ∀ xs : List Nat,
    affine 1 0 1 2 xs = 0 * xs.sum + 2 * xs.length + 1 := by
  apply certify <;> decide
#print axioms task_007

theorem task_008 : ∀ xs : List Nat,
    affine 2 0 1 2 xs = 0 * xs.sum + 2 * xs.length + 2 := by
  apply certify <;> decide
#print axioms task_008

theorem task_009 : ∀ xs : List Nat,
    affine 0 1 1 0 xs = 1 * xs.sum + 0 * xs.length + 0 := by
  apply certify <;> decide
#print axioms task_009

theorem task_010 : ∀ xs : List Nat,
    affine 1 1 1 0 xs = 1 * xs.sum + 0 * xs.length + 1 := by
  apply certify <;> decide
#print axioms task_010

theorem task_011 : ∀ xs : List Nat,
    affine 2 1 1 0 xs = 1 * xs.sum + 0 * xs.length + 2 := by
  apply certify <;> decide
#print axioms task_011

theorem task_012 : ∀ xs : List Nat,
    affine 0 1 1 1 xs = 1 * xs.sum + 1 * xs.length + 0 := by
  apply certify <;> decide
#print axioms task_012

theorem task_013 : ∀ xs : List Nat,
    affine 1 1 1 1 xs = 1 * xs.sum + 1 * xs.length + 1 := by
  apply certify <;> decide
#print axioms task_013

theorem task_014 : ∀ xs : List Nat,
    affine 2 1 1 1 xs = 1 * xs.sum + 1 * xs.length + 2 := by
  apply certify <;> decide
#print axioms task_014

theorem task_015 : ∀ xs : List Nat,
    affine 0 1 1 2 xs = 1 * xs.sum + 2 * xs.length + 0 := by
  apply certify <;> decide
#print axioms task_015

theorem task_016 : ∀ xs : List Nat,
    affine 1 1 1 2 xs = 1 * xs.sum + 2 * xs.length + 1 := by
  apply certify <;> decide
#print axioms task_016

theorem task_017 : ∀ xs : List Nat,
    affine 2 1 1 2 xs = 1 * xs.sum + 2 * xs.length + 2 := by
  apply certify <;> decide
#print axioms task_017

theorem task_018 : ∀ xs : List Nat,
    affine 0 2 1 0 xs = 2 * xs.sum + 0 * xs.length + 0 := by
  apply certify <;> decide
#print axioms task_018

theorem task_019 : ∀ xs : List Nat,
    affine 1 2 1 0 xs = 2 * xs.sum + 0 * xs.length + 1 := by
  apply certify <;> decide
#print axioms task_019

theorem task_020 : ∀ xs : List Nat,
    affine 2 2 1 0 xs = 2 * xs.sum + 0 * xs.length + 2 := by
  apply certify <;> decide
#print axioms task_020

theorem task_021 : ∀ xs : List Nat,
    affine 0 2 1 1 xs = 2 * xs.sum + 1 * xs.length + 0 := by
  apply certify <;> decide
#print axioms task_021

theorem task_022 : ∀ xs : List Nat,
    affine 1 2 1 1 xs = 2 * xs.sum + 1 * xs.length + 1 := by
  apply certify <;> decide
#print axioms task_022

theorem task_023 : ∀ xs : List Nat,
    affine 2 2 1 1 xs = 2 * xs.sum + 1 * xs.length + 2 := by
  apply certify <;> decide
#print axioms task_023

theorem task_024 : ∀ xs : List Nat,
    affine 0 2 1 2 xs = 2 * xs.sum + 2 * xs.length + 0 := by
  apply certify <;> decide
#print axioms task_024

theorem task_025 : ∀ xs : List Nat,
    affine 1 2 1 2 xs = 2 * xs.sum + 2 * xs.length + 1 := by
  apply certify <;> decide
#print axioms task_025

theorem task_026 : ∀ xs : List Nat,
    affine 2 2 1 2 xs = 2 * xs.sum + 2 * xs.length + 2 := by
  apply certify <;> decide
#print axioms task_026

#eval Lean.versionString
end Leant2Affine
