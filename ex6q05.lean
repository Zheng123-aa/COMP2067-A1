open classical

constant A : Type
constant PP : A → Prop

theorem ex6q05 : ¬ (∀ x : A, PP x) → ∃ x : A, ¬ PP x :=
begin
  assume h,  -- Assumption: Not all x satisfy PP x

  by_contradiction h_not_exists,  -- Suppose the conclusion is not valid: There does not exist an x such that ¬ PP x

  apply h,  -- In order to obtain the contradiction, prove ∀ x, PP x
  assume x,  -- Choose any x

  by_contradiction h_not_pp,  -- Suppose that the statement PP x does not hold.

  apply h_not_exists,  -- The counterexample has created a contradiction.
  existsi x,  -- Existence of construction: ∃ x, ¬ PP x
  exact h_not_pp,  -- This x does not satisfy PP.
end
