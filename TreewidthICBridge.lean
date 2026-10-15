/-!
# TreewidthICBridge — Puente IC-Treewidth

Conecta las dos teorías verificadas del repositorio:

* **`TreewidthCombinatorial`**: treewidth definido constructivamente como `sInf`,
  con `treewidth_pos_of_has_edge` demostrado sin sorry.

* **`GraphInformationComplexity`**: complejidad de información formalizada con
  `graphIC_lower_bound` demostrado sin sorry.

## Resultados principales

`treewidth_ge_sep_card_sub_one`: Para un grafo G cuyo separador S cabe en algún
bag de toda descomposición, `treewidth G ≥ S.card − 1`.

`treewidth_and_IC_lower_bound_from_sep`: Ambas cotas (treewidth y GraphIC)
crecen con el tamaño del separador, estableciendo el puente estructural.

## Estado: 0 sorries — DEMOSTRADO

∞³ 141.7001 Hz - JMMB Ψ
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import TreewidthCombinatorial
import GraphInformationComplexity

namespace TreewidthICBridge

open TreewidthCombinatorial GraphInformationComplexity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Lema base: un separador en un bag implica ancho ≥ |S| − 1 -/

/--
Si el separador `S` está completamente contenido en el bag `t` de la
descomposición `D`, entonces el ancho de `D` es ≥ `S.card − 1`.

**Prueba**: el bag t tiene cardinalidad ≥ S.card, el iSup de tamaños de bags
es ≥ (D.X t).card ≥ S.card, y `decompWidth = iSup − 1 ≥ S.card − 1`.
-/
lemma decompWidth_ge_sep_card_sub_one
    {G : SimpleGraph V} (D : TreeDecomp G)
    (S : Finset V) (t : ℕ) (hS : S ⊆ D.X t) (hpos : S.card ≥ 1) :
    decompWidth D ≥ S.card - 1 := by
  have hcard : (D.X t).card ≥ S.card := Finset.card_le_card hS
  have hiSup : (⨆ s : ℕ, (D.X s).card) ≥ S.card := le_iSup_of_le t hcard
  simp only [decompWidth]
  omega

/-! ## Teorema principal: treewidth ≥ |S| − 1 -/

/--
**Teorema del separador universal**: Si el separador `S` cabe en algún bag
de *toda* descomposición de árbol de G, entonces `treewidth G ≥ S.card − 1`.

**Prueba**: El treewidth es `sInf { decompWidth D | D }`. Todo elemento de
este conjunto verifica `decompWidth D ≥ S.card − 1` por `decompWidth_ge_sep_card_sub_one`.
El `sInf` de un conjunto cuyos elementos son todos ≥ k es a su vez ≥ k
(por `Nat.le_csInf`).
-/
theorem treewidth_ge_sep_card_sub_one
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S : Finset V) (hpos : S.card ≥ 1)
    (h_sep_in_all : ∀ (D : TreeDecomp G), ∃ t, S ⊆ D.X t) :
    treewidth G ≥ S.card - 1 := by
  unfold treewidth
  apply Nat.le_csInf (decompWidth_set_nonempty G)
  intro k ⟨D, hD⟩
  obtain ⟨t, ht⟩ := h_sep_in_all D
  have hbound := decompWidth_ge_sep_card_sub_one D S t ht hpos
  omega

/-! ## Teorema puente: cotas inferiores compartidas -/

/--
**Teorema puente IC-Treewidth** (versión precisa).

Para un grafo G y un separador balanceado S con `S.card ≥ 2`, si S cabe en
algún bag de toda descomposición de árbol de G:

* `treewidth G ≥ S.card − 1`   (cota combinatoria, demostrada arriba)
* `GraphIC G S ≥ S.card / 2`   (cota informacional, de `graphIC_lower_bound`)

Ambas cotas son testificadas por el mismo separador S, estableciendo el
**puente estructural** entre la teoría de treewidth y la complejidad de información.

**Por qué no se prueba `treewidth G ≥ GraphIC G S / 2` directamente**: Las cotas
`treewidth G ≥ S.card − 1` y `GraphIC G S ≥ S.card / 2` van en la misma
dirección (ambas crecen con S.card), pero `treewidth ≥ GraphIC / 2` requeriría
`S.card − 1 ≥ (|V| − S.card) / 2`, i.e., `3 * S.card ≥ |V| + 2`, que no está
garantizado sólo por la hipótesis de separador balanceado. La conexión correcta
es la cota compartida en función del tamaño de S.
-/
theorem treewidth_and_IC_lower_bound_from_sep
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S : Separator G)
    (h_sep : is_balanced_separator G S)
    (h_nonempty : Fintype.card V > 0)
    (h_card2 : S.S.card ≥ 2)
    (h_sep_in_all : ∀ (D : TreeDecomp G), ∃ t, S.S ⊆ D.X t) :
    treewidth G ≥ S.S.card - 1 ∧ GraphIC G S ≥ S.S.card / 2 :=
  ⟨treewidth_ge_sep_card_sub_one S.S (by omega) h_sep_in_all,
   graphIC_lower_bound G S h_sep h_nonempty⟩

/--
**Corolario**: Cuando `S.card ≥ 2`, tanto el treewidth como GraphIC superan
`S.card / 2`, estableciendo que la misma medida de separación acota
ambas complejidades estructurales.
-/
corollary treewidth_and_IC_share_sep_bound
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S : Separator G)
    (h_sep : is_balanced_separator G S)
    (h_nonempty : Fintype.card V > 0)
    (h_card2 : S.S.card ≥ 2)
    (h_sep_in_all : ∀ (D : TreeDecomp G), ∃ t, S.S ⊆ D.X t) :
    treewidth G ≥ S.S.card / 2 ∧ GraphIC G S ≥ S.S.card / 2 := by
  obtain ⟨htw, hIC⟩ := treewidth_and_IC_lower_bound_from_sep S h_sep h_nonempty h_card2 h_sep_in_all
  exact ⟨by omega, hIC⟩

/-! ## Declaración estructural de separación -/

/--
**Separación estructural** (declaración, Brecha B4 parcial).

La existencia de familias de grafos cuyo treewidth crece como Ω(n) mientras
que la complejidad polinomial requeriría treewidth O(log n) es el núcleo de
la separación P ≠ NP en el marco IC-treewidth.

La demostración completa requiere:
- Cerrar Brecha B2 (Bodlaender) y B3 (separadores explícitos).
- Formalizar el gadget Tseitin en familias de expansores.
-/
def treewidth_ic_separation : Prop :=
  ∀ (n : ℕ), n > 0 →
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V) (_ : DecidableRel G.Adj)
      (S : Separator G),
      Fintype.card V = n ∧
      is_balanced_separator G S ∧
      treewidth G ≥ n / 2

/-!
## Resumen de conexiones

```
PathGraphAcyclic.lean
        ↓ (acyclicity of path graphs)
TreewidthCombinatorial.lean      GraphInformationComplexity.lean
        ↓                                    ↓
        └──────── TreewidthICBridge.lean ────┘
                         ↓
     treewidth_ge_sep_card_sub_one          (0 sorry)
     treewidth_and_IC_lower_bound_from_sep  (0 sorry)
     treewidth_and_IC_share_sep_bound       (0 sorry)
     treewidth_ic_separation                (declaración, B4 en progreso)
```

∞³ 141.7001 Hz - JMMB Ψ
-/

end TreewidthICBridge
