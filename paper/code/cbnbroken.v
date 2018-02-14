Inductive step : configuration → configuration → Prop :=
  | Id : ∀ M N y x Φ Ψ Ψ', 
             ⟨Ψ, x ↦ M, Φ⟩M ⇓ ⟨Ψ'⟩:λy,N →
          ⟨Ψ, x ↦ M, Φ⟩ x ⇓ ⟨Ψ', x ↦ :λy,N, Φ⟩:λy,N
  | Abs : ∀ N x Φ, ⟨Φ⟩:λx,N ⇓ ⟨Φ⟩:λx,N
  | App : ∀ M N L B y x x' Φ Ψ Υ,
         x' ∉ vars N ++ domain Ψ → 
            ⟨Φ⟩L ⇓ ⟨Ψ⟩:λx,N → 
      ⟨Ψ, x' ↦ M⟩[x'//x]N ⇓ ⟨Υ⟩:λy,B →
           ⟨Φ⟩(L@M) ⇓ ⟨Υ⟩:λy,B
where " c1 '⇓' c2 " := (step c1 c2).
