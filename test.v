Goal 0 <> 1.
Proof.
  intro.
  About H.
  change (match 0 with
                   | 0 => False
                   | _ => True
                   end).
  rewrite H.
  split.
Qed.
