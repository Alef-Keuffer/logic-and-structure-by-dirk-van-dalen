# logic-and-structure-by-dirk-van-dalen
My journey reading Logic and Structure by Dirk van Dalen

## Q01

On Page 8, what is this technique of "From the form of the expressions it is clear that [...] look at the brackets, [...]"?

## Did not understand (DNU01)

Page 8, proof of theorem 2.1.3. Suppose I rewrote the theorem to remove $(iii)$ and left the proof stay the same. What part of the proof would be wrong? I think the proof is handwavy.

## Page 9, proof of 2 left for the reader

$(iii)$ let $φ₀,…,φₙ$ be a formation sequence of $φ$. Then, $φ₀,…,φₙ,(¬φₙ)$ is a formation sequence of $(¬φₙ)$.

## Note on proof of Thm. 2.1.5

haha, the last two sentences.

## Regarding Thm. 2.1.6

Is there an example where definition by recursion does not give rise to exactly one mapping? Have to write down an example later.

## Note on Thm. 2.1.8

Shows how to prove equivalence between two inductions.

## On Thm.2.1.8

Why do they have to show $∀φB(φ)$?

## P014E01

Formation sequences.

$$(¬p₂ → (p₃ ∨ (p₁ ↔ p₂))) ∧ ¬p₃$$

$p₁,p₂,(p₁ ↔ p₂),p₃\\,(p₃ ∨ (p₁ ↔ p₂)),¬p₂\\,(¬p₂ → (p₃ ∨ (p₁ ↔ p₂))),¬p₃\\,(¬p₂ → (p₃ ∨ (p₁ ↔ p₂))) ∧ ¬p₃$

$$(p₇ → ¬⊥) ↔ ((p₄ ∧ ¬p₂) → p₁)$$

$⊥,¬⊥,p₇,(p₇ → ¬⊥),p₄,p₂¬p₂\\,(p₄ ∧ ¬p₂),p₁\\,((p₄ ∧ ¬p₂) → p₁)\\,(p₇ → ¬⊥) ↔ ((p₄ ∧ ¬p₂) → p₁)$

$$(((p₁→p₂)→p₁)→p₂)→p₁$$

$p₁,p₂,(p₁→p₂),(p₁→p₂)→p₁\\,(((p₁→p₂)→p₁)→p₂)\\,(((p₁→p₂)→p₁)→p₂)→p₁$

## P014E02

Show that $((→ ∉ \text{PROP}$.

Suppose $((→ ∈ X$ and that $X$ satisfies $\text{(i), (ii), (iii)}$ of Def. 2.1.2. 

We claim $Y=X-\{((→\}$ also satisfies $\text{(i), (ii), (iii)}$.

Since $⊥,pᵢ ∈ X$ and $⊥ ≠ ((→$ and $pᵢ ≠ ((→$, also $⊥,pᵢ ∈ Y$. Thus, $Y$ satisfies $\text{(i)}$.

If $φ,ψ ∈ Y$, then $φ,ψ ∈ X$, because $Y ⊆ X$. Since $X$ satisfies $\text{(ii)}$, $(φ\square ψ) ∈ X$. Since $(φ\square ψ) ≠ ((→$, $(φ\square ψ) ∈ X - \{((→\} = Y$. Thus, $Y$ satisfies $\text{(ii)}$.

If $φ∈Y$, then $φ∈X$, because $Y⊆X$. Since $X$ satisfies $\text{(iii)}$, $(¬φ) ∈ X$. Since $(¬φ) ≠ ((→$, $(¬φ) ∈ Y$. Thus, $Y$ satisfies $\text{(iii)}$.

So $Y$ satisfies $\text{(i), (ii), (iii)}$ and is smaller than $X$. Hence $X$ is not the smallest set satisfying $\text{(i), (ii), (iii)}$, so $((→$ cannot belong to $\text{PROP}$.

## P014E03

Show that the relation "is a subformula of" is transitive.

$ψ$ is a subformula of $φ$ if $ψ∈Sub(φ)$.

The set of subformulas $Sub(φ)$ is

1. $Sub(φ) = \{φ\}$ for atomic $φ$;
2. $Sub(φ₁\square φ₂) = Sub(φ₁) ∪ Sub(φ₂) ∪ \{φ₁\square φ₂\}$;
3. $Sub(¬φ) = Sub(φ) ∪ \{¬φ\}$.

A binary relation $R$ on a set $X$ is transitive if $$∀_{a,b,c ∈ X}: aRb ∧ bRc ⟹ aRc$$

Suppose $α$ is a subformula of $β$ and $β$ is a subformula of $γ$ and $α,β,γ ∈ \text{PROP}$.

In other words,

- $α ∈ Sub(β)$
- $β ∈ Sub(γ)$

and we wish to show $α ∈ Sub(γ)$.

Observe that $Sub(α) ⊆ Sub(β)$ and $Sub(β) ⊆ Sub(γ)$. So we have

$$Sub(α) ⊆ Sub(β) ⊆ Sub(γ)$$

Obviously, $α ∈ Sub(α)$. So, by the transitivity of set inclusion, $α∈Sub(γ)$.

## P014E04

Let $φ$ be a subformula of $ψ$. Show that $φ$ occurs in each formation sequence of $ψ$.

Let $ψ$ have a formation sequence $ψ₀,…,ψₙ$.

$n=0: ψ=ψ₀$. By the definition of formation sequences, $ψ$ is atomic. So, by the definition of subformulas, $Sub(ψ)=\{ψ\}$. So, $φ=ψ=ψ₀∈\{ψ\}=\{ψ₀\}=\{φ\}$.

Suppose that all formation sequences of length $m<n$ satisfy the property. By definition,

1. $ψₙ=(ψⱼ \square ψₖ)$ for $j,k<n$, or
2. $ψₙ=(¬ψⱼ)$ for $j<n$, or
3. $ψₙ$ is atomic.

In the first case $ψⱼ$ and $ψₖ$ have formation sequences of length $j,k<n$, so by the induction hypothesis  $φ∈Sub(ψⱼ) ⟹ φ=ψₐ$ $(a≤j)$, $φ∈Sub(ψₖ) ⟹ φ=ψ_b$ $(b≤k)$. Either case satisfies our conclusion. Negation is simlar. Atomic case is trivial.

Note that if $φ∉Sub(ψⱼ) ∧ φ∉Sub(ψₖ)$, then $φ=ψₙ∈Sub(ψₙ)=Sub(ψ)$.

## P014E05

If $φ$ occurs in a shortest formation sequence of $ψ$ then $φ$ is a subformula of $ψ$.

Let $SF_{SET}(ψ)=\{ψᵢ:ψ₀,…,ψₙ \text{ is a shortest formation sequence of } ψ ∧ 0≤i≤n\}$.

Observe that,

- $SF_{SET}(ψᵢ) ⊆ SF_{SET}(ψₙ)$
- $SF_{SET}(ψ) = Sub(ψ)$
- $⋃SF_{SET}(ψ) = SF_{SET}(ψ)$

$SF_{SET}(ψ)$ reads shortest formation set of $ψ$.

Now, the property we want to prove is

$$A(ψ): φ∈SF_{SET}(ψ) ⟹ φ ∈ Sub(ψ)$$

We show $A(ψ)$ by induction on $n$.

Let $ψ₀,…,ψₙ$ be the shortest formation sequence of $ψ$. We show $φ=ψᵢ\ (i≤n) ⟹ φ ∈ Sub(ψ)$ by induction on $n$.

$n=0: ψ=ψ₀$ and by definition $ψ$ is atomic. So, $Sub(ψ)=Sub(ψ₀)=\{ψ₀\}$. Since $i≤0=n$, $i∈\{0\}$. If $φ=ψ₀$, obviously $Sub(ψ)=Sub(ψ₀)=\{ψ₀\}=\{φ\}$. So $φ∈Sub(ψ)$.

Suppose that all expressions with shortest formation sequences $m<n$ satisfy the property. By definition

1. $ψₙ=(ψⱼ \square ψₖ)$ for $j,k<n$, or
2. $ψₙ=(¬ψⱼ)$ for $j<n$, or
3. $ψₙ$ is atomic.

In the first case, by the induction hypothesis, we have $φ∈SF_{SET}(ψⱼ) ⟹ φ ∈ Sub(ψⱼ)$, $φ∈SF_{SET}(ψₖ) ⟹ φ ∈ Sub(ψₖ)$. Note that $j,k < n$. Observe that $SF_{SET}(ψⱼ) ∪ SF_{SET}(ψₖ) ∪ \{ψⱼ\square ψₖ\} = SF_{SET}(ψₙ)$. That means,


$$\underbrace{φ∈SF_{SET}(ψⱼ) ∨ φ∈SF_{SET}(ψₖ)}_{
    \text{prove } A(ψ)\text{ using ind.hyp.}
}
∨ \underbrace{φ∈\{ψⱼ\square ψₖ\}}_{\substack{
    \text{by def. of subformulas }\\
    Sub(ψₙ)\\
    = Sub(ψⱼ\square ψₖ) \\
    = Sub(ψⱼ) ∪ Sub(ψₖ) ∪ \{ψⱼ\square ψₖ\}\\
    \text{ so, } φ∈Sub(ψ)
}}
⟹ φ ∈ SF_{SET}(ψₙ)$$

The second case is similar. The third case degenarates to the base case because the shortest formation sequence of an atomic proposition is when $n=0$.