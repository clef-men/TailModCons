From stdpp Require Import countable gmap infinite numbers.

From iris.algebra Require Export ofe.

Open Scope Z.

Definition loc := Z.

Instance loc_eq_decision : EqDecision loc := Z_eq_dec.
Instance loc_inhabited : Inhabited loc := Z_inhabited.
Instance loc_countable : Countable loc := Z_countable.
Instance loc_infinite : Infinite loc := Z_infinite.

Definition fresh_locs (ls : gset loc) :=
  set_fold (λ k r, (1 + k) `max` r) 1 ls
.

Lemma fresh_locs_fresh ls i :
  0 ≤ i → (fresh_locs ls + i) ∉ ls
.
Proof.
  intros Hi. cut (∀ l, l ∈ ls → l < (fresh_locs ls) + i).
  { intros help Hf%help. simpl in *. lia. }
  apply (set_fold_ind_L (λ r ls, ∀ l, l ∈ ls → l < r + i));
    set_solver by eauto with lia.
Qed.

Global Opaque fresh_locs.

Canonical Structure locO SI := leibnizO SI loc.
