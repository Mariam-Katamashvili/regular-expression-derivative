# Fuzzifying Derivatives of Regular Expressions

This repository contains a paper and Rocq formalization about derivatives of regular expressions, derivative-based automata construction, and the extension of these ideas to fuzzy similarity relations.

The central idea is the following: ordinary Brzozowski derivatives describe how a regular expression changes after consuming an input symbol or word. This gives a direct way to construct deterministic finite automata, where each state is a derivative of the original expression. The paper extends this picture toward a fuzzy setting, where symbols are not matched only by exact equality but also by a similarity relation and a fixed cut value.

The repository has two main parts:

- `tex/` — the mathematical paper.
- `coq/` — the Rocq formalization of the main definitions, constructions, and proofs from the paper.

## Paper overview

The paper develops the theory in the following order.

1. **Basic definitions**

   The paper defines alphabets, words, languages, regular expressions, semantic interpretation, nullability, canonical forms, and semantic equivalence.

2. **Classical derivatives**

   It defines semantic derivatives of languages, syntactic derivatives of regular expressions, proves the semantic-syntactic correspondence theorem, and states regularity and finiteness results.

3. **Derivative automata**

   It constructs a deterministic finite automaton from a regular expression using derivatives. The states are canonical representatives of derivative expressions.

4. **Fuzzy proximity and similarity**

   It introduces fuzzy relations, proximity relations, similarity relations, similarity on words, similarity on languages, and syntactic similarity on restricted regular expressions.

5. **Fuzzy derivatives**

   It defines fuzzy derivatives of languages and regular expressions using a similarity relation and a cut value. It also relates fuzzy derivatives to ordinary derivatives over a quotient alphabet.

## Paper-to-Rocq map

The following table maps the main definitions, lemmas, propositions, and theorems from the paper to their Rocq locations.

### Section 2: Basic Definitions

| Paper item | Rocq formalization |
|---|---|
| Definition: Alphabet, words, and languages | Alphabet: `coq/src/Alphabet.v`, module types `SYM`, `OSYM`, `FINSYM`, `OFINSYM`. Words and languages: `coq/src/Languages.v`, definitions `word`, `language`. Language operations: `coq/src/Languages.v`, definitions `void`, `eps`, `atom`, `plus`, `conc`, `star`, `prod`, `compl` |
| Definition: (Restricted) Regular Expressions | `coq/src/RegexSemantics.v`, inductive definition `regex`; definition `restricted_regex` |
| Definition: Semantic interpretation | `coq/src/RegexSemantics.v`, definition `den`; language-side definitions imported from `coq/src/Languages.v`: `void`, `eps`, `atom`, `plus`, `conc`, `star`, `prod`, `compl` |
| Definition: Nullable regular expressions | `coq/src/Nullable.v`, definitions `has_eps`, `nu`; proofs `nullable_correct`, `mem_nu` |
| Definition: Semantic equivalence | `coq/src/RegexSemantics.v`, definitions `lang_eq`, `re_equiv`, `semantic_equiv`; proofs `lang_eq_refl`, `lang_eq_sym`, `lang_eq_trans`, `re_equiv_refl`, `re_equiv_sym`, `re_equiv_trans` |
| Definition: Similarity (`~`) | `coq/src/Canonicalization.v`, definitions `nf`, `similar`; normalization definitions `mkPlus`, `mkConc`, `mkStar`, `mkAnd`, `mkNot`, `canonize`, `eq_regex` |
| Lemma: Canonicalization/Normalization | `coq/src/CanonicalizationCorrectness.v`, theorem/proof `similar_iff_nf_eq`; supporting proofs `eq_regex_sound`, `eq_regex_refl`, `eq_regex_complete` |
| Lemma: Soundness of normalization | `coq/src/CanonicalizationCorrectness.v`, theorem/proof `similar_sound`; supporting proof `canonize_correct` |

### Section 3: Fuzzy Relations and T-Similarity

| Paper item | Rocq formalization |
|---|---|
| Definition (Appendix): T-norm (left-continuous) | `coq/src/SimilarityRelations.v`, record `tnorm` (left-continuity: field `tn_lcont`); supporting proofs `tn_mono_r`, `tn_mono2`, `tn_idem_le`, `tn_le_l`, `tn_le_r`, `tn_0l`, `tn_0r`, `tn_shuffle`, `tn_idem_min` |
| Definition: Fuzzy relation, cut, T-similarity, Gödelian | `coq/src/SimilarityRelations.v`, definitions `fuzzy_rel`, `cut_value`, `mu_cut`, `is_T_similarity`, `is_godelian`; the paper's min-based Gödelian definition is `is_godelian_min`, shown equivalent by `is_godelian_minP` |
| Lemma: μ-cuts of T-similarity relations are equivalences | `coq/src/SimilarityRelations.v`, proofs `T_equivalence_idem` (item 1), `T_equivalence_godelian` (item 2) |
| Definition: T-similarity on Regular Expressions - General T-norm | `coq/src/SimilarityRelations.v`, definition `RE`; star clause via `tpow`, `InfN`; clause equations `RE_refl`, `RE_Char`, `RE_Alt`, `RE_Seq`, `RE_Star`, `RE_otherwise`; supporting proofs `RE_range`, `InfN_lower`, `InfN_greatest` |
| Definition: T-similarity on Words - General T-norm | `coq/src/SimilarityRelations.v`, definition `RwT`; supporting proof `RwT_range` |
| Definition: T-similarity on languages - General T-norm | `coq/src/SimilarityRelations.v`, definition `RLT`, built from `supRwT` and `hausRwT` (the second infimum is taken over `R^w(w2,w1)`, which equals `R^w(w1,w2)` by `RwT_sym`) |
| Lemma: `R^E`, `R^w`, `R^L` are T-similarities | `coq/src/SimilarityRelations.v`, theorems `RE_is_T_similarity` (item 1, on all of E), `RwT_is_T_similarity` (item 2), `RLT_is_T_similarity` (item 3); supporting proofs `RE_sym`, `RE_trans`, `RE_trans_degenerate`, `RwT_refl`, `RwT_sym`, `RwT_trans`, `hausRwT_refl`, `hausRwT_trans`, `tn_supRwT` (uses left-continuity), `tpow_mono`, `tpow_T` |
| Lemma: Gödelian transfer to `R^w`, `R^E`, `R^L` | `coq/src/SimilarityRelations.v`, theorems `RwT_godelian`, `RE_godelian`, `RLT_godelian` (for a finite alphabet, the paper's standing assumption); supporting proofs `RE_01`, `tpow_idem`, `InfN_tpow_idem`, `finite_max`, `finite_min`, `SupL_attained`, `InfL_attained`, `RLT_values_spec`, `RLT_in_values` |
| Lemma: positive `R^E` forces a common skeleton | `coq/src/SimilarityRelations.v`, theorem `RE_pos_skeleton`; definitions `skeleton`, `holes`, `fill`; supporting proofs `RE_pos_skel_of`, `fill_skel_of`, `size_syms_of`, `tn_pos` |
| Definition: Fuzzy semantic interpretation `L^μ` | `coq/src/SimilarityRelations.v`, definition `fuzzy_den` |
| Theorem 3.1(1): `R^E(r1,r2) ≤ R^L(L(r1),L(r2))` | `coq/src/SimilarityRelations.v`, theorem `RE_le_RLT` (on all of E, for every T-norm; left-continuity is not used); supporting proofs `RwT_cat`, `RE_witness_degenerate`, `RE_witness`, `RE_le_hausRwT` |
| Theorem 3.1(2): `R^L` as a sup of `R^E` over equivalent expressions | todo |
| Theorem 3.1, "moreover": `R^E(r1,r2) ≥ μ` gives `L^μ(r1) = L^μ(r2)` when `R` is Gödelian or `μ ⊗ μ = μ` | `coq/src/SimilarityRelations.v`, theorem `RE_cut_fuzzy_den_eq` (on all of E); supporting proofs `RwT_cut_equivalence`, `fuzzy_den_sub` |
| Lemma: Finite Syntactic Similarity | `coq/src/SimilarityRelations.v`, theorem `RE_nonzero_finite`; definition `sym_seqs`; supporting proofs `sym_seqs_complete`, `In_map_mem`, `RE_pos_skel_of` |

### Section 4: Derivatives and their Fuzzification

| Paper item | Rocq formalization |
|---|---|
| Definition: Semantic derivative `∂_a(L)`, `∂_u(L)` | `coq/src/Derivatives.v`, definitions `dlang_char`, `dlang`; proofs `dlang_nil`, `dlang_cat`, `dlang_correct`, `dlang_charE` |
| Definition: Syntactic derivative `D_a(r)`, `D_u(r)` | `coq/src/Derivatives.v`, definitions `D_char`, `D`; proofs `D_nil`, `D_cat` |
| Theorem 4.1(1): `u ∈ L(r)` iff `ε ∈ D_u(r)` | `coq/src/Derivatives.v`, theorem `D_eps_correct`; nullability form `D_nullable` (`has_eps (D u r) = (u \in r)`) |
| Theorem 4.1(2): `∂_u(L)` is regular | `coq/src/Derivatives.v`, theorem `derivative_regular` |
| Theorem 4.1(3): `L(D_u(r)) = ∂_u(L(r))` | `coq/src/Derivatives.v`, theorem `D_correct`; supporting proof `D_char_correct` |
| Theorem 4.1(4): syntactic finiteness up to canonicalization | todo |
| Theorem 4.1(5): semantic finiteness | todo |
| Definition 4.4: `μ`-fuzzy semantic derivative `∂_a^μ(L)` | `coq/src/FuzzyDerivatives.v`, definition `fdlang_char` |
| Definition 4.5: `μ`-fuzzy syntactic derivative `D_a^μ(r)` | `coq/src/FuzzyDerivatives.v`, definition `Dmu_char` (a finite sum `sum_re` over the alphabet and `RE_candidates`); membership lemma `Dmu_charP` |
| Definition 4.6: `μ`-fuzzy semantic derivative by a word `∂_u^μ(L)` | `coq/src/FuzzyDerivatives.v`, definition `fdlang` |
| Definition 4.7: `μ`-fuzzy syntactic derivative by a word `D_u^μ(r)`, with the value sets `Λ` of the remark after it | `coq/src/FuzzyDerivatives.v`, definitions `Dmu`, `Lambda`, `Lambda_char`; lemmas `Dmu_consP`, `Lambda_charP`, `Lambda_in01` |
| Theorem 4.2(1): experimentum crucis, `u ∈ L^μ(r)` iff `ε ∈ L(D_u^μ(r))` | `coq/src/FuzzyDerivatives.v`, theorem `experimentum_crucis` (for every T-norm, on all of E, finite alphabet); supporting proofs `Dmu_eps_sound`, `Dmu_eps_complete`, `Dmu_antitone` |
| Theorem 4.2(2): `D_a^μ(r)` is a regular expression | by construction: `Dmu_char` returns a `regex`; regularity of `∂_a^μ(L)` is todo |
| Theorem 4.2(3): `L(D_a^μ(r)) ⊆ ∂_a^μ(L(r))` | `coq/src/FuzzyDerivatives.v`, theorem `Dmu_char_sound` (for every T-norm, on all of E) |
| Theorem 4.2(4)–(6): finiteness and decidability | todo |
| Proposition 4.1: `μ`-cuts of `R`, `R^E`, `R^w`, `R^L` are equivalences when `R` is Gödelian or `μ ⊗ μ = μ` | `coq/src/SimilarityRelations.v`, theorems `R_cut_equivalence` (item 1), `RE_cut_equivalence` (item 2, on all of E), `RwT_cut_equivalence` (item 3), `RLT_cut_equivalence` (item 4; the `μ ⊗ μ = μ` case for any alphabet is `RLT_cut_equivalence_idem`, the Gödelian case needs a finite alphabet) |
| Proposition 4.2: simplified fuzzy derivatives when `μ`-cuts are equivalences | todo |
| Definition: quotient alphabet `Σ^μ`, maps `q_μ`, `q_μ*`, quotient language `[L]_μ` | todo |
| Proposition 4.3: fuzzy derivative via the quotient alphabet | todo |
| Proposition 4.4: `L(D_a^μ(r)) ⊆ ∂_a^μ(L(r))` via the quotient alphabet | todo |

| Paper item | Paper location | Rocq location |
|---|---|---|
| Alphabet `Σ` | `tex/sections/preliminaries.tex` | `coq/src/Alphabet.v` |
| Words `Σ*` | `tex/sections/preliminaries.tex` | `coq/src/Languages.v`, `word := seq A` |
| Languages `L ⊆ Σ*` | `tex/sections/preliminaries.tex` | `coq/src/Languages.v`, `language := pred word` |
| Empty language | `tex/sections/preliminaries.tex` | `coq/src/Languages.v`, `void`; `coq/src/RegexSemantics.v`, `Empty` |
| Empty word language `{ε}` | `tex/sections/preliminaries.tex` | `coq/src/Languages.v`, `eps`; `coq/src/RegexSemantics.v`, `Eps` |
| Atomic language `{a}` | `tex/sections/preliminaries.tex` | `coq/src/Languages.v`, `atom`; `coq/src/RegexSemantics.v`, `Char` |
| Union of languages | `tex/sections/preliminaries.tex` | `coq/src/Languages.v`, `plus`; `coq/src/RegexSemantics.v`, `Alt` |
| Concatenation of languages | `tex/sections/preliminaries.tex` | `coq/src/Languages.v`, `conc`; `coq/src/RegexSemantics.v`, `Seq` |
| Kleene star | `tex/sections/preliminaries.tex` | `coq/src/Languages.v`, `star`; `coq/src/RegexSemantics.v`, `Star` |
| Intersection | `tex/sections/preliminaries.tex` | `coq/src/Languages.v`, `prod`; `coq/src/RegexSemantics.v`, `And` |
| Complement | `tex/sections/preliminaries.tex` | `coq/src/Languages.v`, `compl`; `coq/src/RegexSemantics.v`, `Neg` |
| Regular-expression grammar | `tex/sections/preliminaries.tex` | `coq/src/RegexSemantics.v`, inductive type `regex` |
| Semantic interpretation `L(r)` | `tex/sections/preliminaries.tex` | `coq/src/RegexSemantics.v`, `den` |
| Semantic equivalence `r ≡ s` | `tex/sections/preliminaries.tex` | `coq/src/RegexSemantics.v`, `re_equiv`, notation `r ≈ s` |
| Nullable function `ν` | `tex/sections/preliminaries.tex` | `coq/src/Nullable.v`, `has_eps`, `nullable`, `nu` |
| Correctness of nullable | `tex/sections/preliminaries.tex` | `coq/src/Nullable.v`, `nullable_correct` |
| Membership in `ν(r)` | `tex/sections/preliminaries.tex` | `coq/src/Nullable.v`, `mem_nu` |
| Canonical form `[r]` | `tex/sections/preliminaries.tex` | `coq/src/Canonicalization.v`, `canonize` |
| Normalization function `nf` | `tex/sections/preliminaries.tex` | `coq/src/Canonicalization.v`, `canonize` |
| Syntactic equality after canonicalization | `tex/sections/preliminaries.tex` | `coq/src/Canonicalization.v`, `same_after_canon` |
| Soundness of normalization | `tex/sections/preliminaries.tex` | `coq/src/CanonicalizationCorrectness.v`, `canonize_correct`, `canonize_equiv` |
| Derivative of a language by a symbol `∂a(L)` | `tex/sections/derivative_regex_reglanguages.tex` | `coq/src/Derivatives.v`, `dlang_char` |
| Derivative of a language by a word `∂u(L)` | `tex/sections/derivative_regex_reglanguages.tex` | `coq/src/Derivatives.v`, `dlang` |
| Semantic derivative laws | `tex/sections/derivative_regex_reglanguages.tex` | `coq/src/Derivatives.v`, `dlang_nil`, `dlang_cat`, `dlang_correct`, `dlang_charE` |
| Syntactic derivative by a symbol `D_a(r)` | `tex/sections/derivative_regex_reglanguages.tex` | `coq/src/Derivatives.v`, `D_char` |
| Syntactic derivative by a word `D_u(r)` | `tex/sections/derivative_regex_reglanguages.tex` | `coq/src/Derivatives.v`, `D` |
| Derivative rules for `∅`, `ε`, letters, `+`, `·`, `*`, `&`, `¬` | `tex/sections/derivative_regex_reglanguages.tex` | `coq/src/Derivatives.v`, `D_char` |
| Rule `D_ε(r)=r` | `tex/sections/derivative_regex_reglanguages.tex` | `coq/src/Derivatives.v`, `D_nil` |
| Rule `D_{uv}(r)=D_v(D_u(r))` | `tex/sections/derivative_regex_reglanguages.tex` | `coq/src/Derivatives.v`, `D_cat` |
| Single-symbol derivative correctness | `tex/sections/derivative_regex_reglanguages.tex` | `coq/src/Derivatives.v`, `D_char_correct` |
| Semantic-syntactic correspondence for classical derivatives | `tex/sections/derivative_regex_reglanguages.tex` | `coq/src/Derivatives.v`, `D_correct` |
| Regularity preservation for classical derivatives | `tex/sections/derivative_regex_reglanguages.tex` | `coq/src/Derivatives.v`, `regular`, `derivative_regular` |
| Finiteness of classical derivative languages | `tex/sections/derivative_regex_reglanguages.tex` | todo — proved only in paper and yet to be formalized |
| Derivative DFA states `[D_u(r)]` | `tex/sections/automata_construction.tex` | `coq/src/Automata.v`, `constructed_dfa`; `coq/src/AutomataConstruction.v`, `state`, `construct_dfa` |
| DFA transition `δ(q,a)=[D_a(q)]` | `tex/sections/automata_construction.tex` | `coq/src/Automata.v`, `constructed_dfa`; `coq/src/AutomataConstruction.v`, `canonical_derivative`, `step` |
| Initial DFA state `[r]` | `tex/sections/automata_construction.tex` | `coq/src/Automata.v`, `constructed_dfa`; `coq/src/AutomataConstruction.v`, `construct_dfa` |
| Accepting states via nullability | `tex/sections/automata_construction.tex` | `coq/src/Automata.v`, `constructed_dfa`; `coq/src/AutomataConstruction.v`, `accepting_state`, `final_states` |
| Extension of transition to words `δ*` | `tex/sections/automata_construction.tex` | `coq/src/Automata.v`, `delta_star`; `coq/src/AutomataConstruction.v`, `delta_star` |
| Reached state denotes derivative language | `tex/sections/automata_construction.tex` | `coq/src/Automata.v`, `delta_star_constructed_lang`, `delta_star_constructed_derivative_equiv` |
| DFA correctness theorem `L(M)=L(r)` | `tex/sections/automata_construction.tex` | `coq/src/Automata.v`, `dfa_correctness` |
| Executable DFA construction pseudocode | `tex/sections/automata_construction.tex` | `coq/src/AutomataConstruction.v`, `goto`, `construct_dfa` |
| Correctness of executable DFA construction | `tex/sections/automata_construction.tex` | todo |
| DFA minimality theorem | `tex/sections/automata_construction.tex` | todo — proved only in paper and yet to be formalized |
| Fuzzy relation `S × S -> [0,1]` | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `simval`, `fuzzy_rel` |
| Minimum T-norm | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `smin` |
| Cut value | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `cut_value` |
| μ-cut relation | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `mu_cut` |
| Proximity relation | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `is_proximity` |
| Similarity relation | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `is_similarity` |
| Similarity on words `R^w` | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `RwT` (general T-norm) |
| `R^w` is reflexive | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `RwT_refl` |
| `R^w` is symmetric | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `RwT_sym` |
| `R^w` is transitive under minimum T-norm | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `RwT_trans` (for every T-norm) |
| `R^w` is a similarity relation | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `RwT_is_T_similarity` |
| Similarity on languages `R^L` | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `RLT`, `SupL`, `InfL` |
| `R^L` is a similarity relation | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `RLT_is_T_similarity` |
| Restricted regular expressions | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/RegexSemantics.v`, `restricted_regex` |
| Syntactic similarity on regex `R^e` | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `RE` (general T-norm) |
| `R^e` is a similarity relation | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `RE_is_T_similarity` |
| Syntax-to-semantics inequality `R^e(r,s) ≤ R^L(L(r),L(s))` | `tex/sections/fuzzy_proximity_similarity_relation.tex` | `coq/src/SimilarityRelations.v`, `RE_le_RLT` |
| Bridge theorem between `R^e` and `R^L` | `tex/sections/fuzzy_proximity_similarity_relation.tex` | todo (Theorem 3.1(2) in `dhkm.tex`) |
| Fuzzy language derivative `∂^μ_a(L)` | `tex/sections/fuzzy_similarity_derivative.tex` | todo |
| μ-cut equivalence on symbols | `tex/sections/fuzzy_similarity_derivative.tex` | todo — proved only in paper and yet to be formalized |
| μ-cut equivalence on words | `tex/sections/fuzzy_similarity_derivative.tex` | todo — proved only in paper and yet to be formalized |
| Quotient alphabet `Σ^μ` | `tex/sections/fuzzy_similarity_derivative.tex` | todo |
| Quotient map `q_μ` and word extension `q_μ*` | `tex/sections/fuzzy_similarity_derivative.tex` | todo |
| Quotient language `L^μ` | `tex/sections/fuzzy_similarity_derivative.tex` | todo |
| Quotient theorem for fuzzy derivatives | `tex/sections/fuzzy_similarity_derivative.tex` | todo — proved only in paper and yet to be formalized |
| Fuzzy derivative by a word | `tex/sections/fuzzy_similarity_derivative.tex` | todo |
| Cut neighborhood `S_a^μ` | `tex/sections/fuzzy_similarity_derivative.tex` | todo |
| Fuzzy expression derivative `D_a^μ(r)` | `tex/sections/fuzzy_similarity_derivative.tex` | todo |
| Fuzzy expression derivative by a word `D_u^μ(r)` | `tex/sections/fuzzy_similarity_derivative.tex` | todo |
| Regularity preservation for fuzzy derivatives | `tex/sections/fuzzy_similarity_derivative.tex` | todo — proved only in paper and yet to be formalized |
| Semantic-syntactic correspondence for fuzzy derivatives | `tex/sections/fuzzy_similarity_derivative.tex` | todo — proved only in paper and yet to be formalized |
| Finiteness of fuzzy derivative languages | `tex/sections/fuzzy_similarity_derivative.tex` | todo — proved only in paper and yet to be formalized |
| Finiteness of fuzzy regex derivative types | `tex/sections/fuzzy_similarity_derivative.tex` | todo — proved only in paper and yet to be formalized |
| Fuzzy DFA correctness | `tex/sections/fuzzy_similarity_derivative.tex` | todo — proved only in paper and yet to be formalized |

## Current formalization work

We are currently working on formalizing the remaining paper-level definitions and results, including the fuzzy-derivative constructions, quotient-language results, fuzzy semantic-syntactic correspondence, finiteness theorems, and fuzzy DFA correctness.
