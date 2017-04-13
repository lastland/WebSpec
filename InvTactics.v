Tactic Notation "solve_by_inversion_step" tactic(t) :=
  match goal with
  | H : _ |- _ => solve [ inversion H; subst; t ]
  end
  || fail "because the goal is not solvable by inversion.".

Tactic Notation "solve" "by" "inversion" "1" :=
  solve_by_inversion_step idtac.
Tactic Notation "solve" "by" "inversion" "2" :=
  solve_by_inversion_step (solve by inversion 1).
Tactic Notation "solve" "by" "inversion" "3" :=
  solve_by_inversion_step (solve by inversion 2).
Tactic Notation "solve" "by" "inversion" "4" :=
  solve_by_inversion_step (solve by inversion 3).
Tactic Notation "solve" "by" "inversion" "5" :=
  solve_by_inversion_step (solve by inversion 4).
Tactic Notation "solve" "by" "inversion" "6" :=
  solve_by_inversion_step (solve by inversion 5).
Tactic Notation "solve" "by" "inversion" "7" :=
  solve_by_inversion_step (solve by inversion 6).
Tactic Notation "solve" "by" "inversion" :=
  solve by inversion 1.
