from pathlib import Path

path = Path("proof/Phil/Surface/GrammarDeterminacyDelimiterBalance.v")
source = path.read_text()

marker = '''Definition delimiter_alternative_balanced_fuel
'''
lemma = '''Lemma delimiter_sequence_fold_none :
  forall fuel items,
    List.fold_left
      (fun state item =>
        match state with
        | Some current_depth =>
            delimiter_effect_fuel fuel current_depth item
        | None => None
        end)
      items None = None.
Proof.
  intros fuel items.
  induction items as [| item items IH].
  - reflexivity.
  - simpl.
    exact IH.
Qed.

'''
if source.count(marker) != 1:
    raise SystemExit(f"expected one alternative definition marker, got {source.count(marker)}")
source = source.replace(marker, lemma + marker, 1)

old = '''        destruct (delimiter_effect_fuel fuel depth item)
          as [middle_depth |] eqn:Hitem; try discriminate.
        pose proof
          (IH item depth middle_depth extra Hitem)
          as Hitem_shift.
        rewrite Hitem_shift.
        exact (IHitems middle_depth final_depth Heffect).
'''
new = '''        destruct (delimiter_effect_fuel fuel depth item)
          as [middle_depth |] eqn:Hitem.
        { pose proof
            (IH item depth middle_depth extra Hitem)
            as Hitem_shift.
          rewrite Hitem_shift.
          exact (IHitems middle_depth final_depth Heffect).
        }
        { rewrite delimiter_sequence_fold_none in Heffect.
          discriminate Heffect.
        }
'''
if source.count(old) != 1:
    raise SystemExit(f"expected one sequence shift block, got {source.count(old)}")
source = source.replace(old, new, 1)

path.write_text(source)
