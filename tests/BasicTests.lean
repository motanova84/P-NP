/-
Basic verification tests
-/

-- Test that basic logic works
example : True := by trivial

example : 1 + 1 = 2 := by native_decide

-- Test that we can import the main library
example : True := by
  have : True := by trivial
  exact this
