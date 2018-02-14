Inductive step : configuration → configuration → Prop :=
  | Id : ∀ M N y x Φ Υ Ψ Ψ', 
             ⟨Ψ & x ↦ M, Φ, Υ⟩M ⇓ ⟨Ψ' & x ↦ M, Φ, Υ⟩:λy,N →
            ⟨Ψ, x ↦ M, Φ & Υ⟩ x ⇓ ⟨Ψ', x ↦ :λy,N, Φ & Υ⟩:λy,N
  | Abs : ∀ N x Φ Ψ, ⟨Ψ & Φ⟩:λx,N ⇓ ⟨Ψ & Φ⟩:λx,N
  | App : ∀ M N L B y x x' Φ Ψ Υ Φ',
         x' ∉ vars N ++ domain (Ψ ++ Φ') → 
            ⟨Φ & Ψ⟩L ⇓ ⟨Φ' & Ψ⟩:λx,N → 
      ⟨Φ', x' ↦ M & Ψ⟩[x'//x]N ⇓ ⟨Υ & Ψ⟩:λy,B →
           ⟨Φ & Ψ⟩(L@M) ⇓ ⟨Υ & Ψ⟩:λy,B
where " c1 '⇓' c2 " := (step c1 c2).
