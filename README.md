# P = NP

[![verifica](https://github.com/vjt/pnp/actions/workflows/verifica.yml/badge.svg)](https://github.com/vjt/pnp/actions/workflows/verifica.yml)

Dimostrazione formale, in Lean 4, che **P = NP**.

- 8.784 righe in 18 file, 1.041 teoremi (973 lemmi generati), 247 definizioni,
  un teorema principale
- una libreria di 17 moduli che si importano a catena, con un diamante in
  mezzo; la radice [`PNP.lean`](PNP.lean) importa e basta
- macchine di Turing col frigo, polinomi di Horner, riduzioni dal divano,
  cicli `for` e `while`, ricorsione ben fondata: un formalizzatore si arrende
  prima della Parte III
- una tattica tutta sua, `disagio`, che gira in tondo prima di chiudere il
  goal (703 teoremi la usano); una notazione tutta sua, `⟪ A ⇝ B in n ↦ n + 1 ⟫`
  (136 enunciati); induttivi mutui, misure di terminazione assurde, un
  diamante di typeclass risolto per priorità, strutture polimorfe negli
  universi, classi di complessità prese a meno di equivalenza col quoziente
- verificata dal kernel: `lake build` è verde, lo dice anche il badge
- zero `sorry`

Pagina del progetto: <https://disagio.sniffo.org/pnp>

Paper (LaTeX, `paper/`, `latexmk -lualatex`): [it](paper/pnp-it.pdf) ·
[en](paper/pnp-en.pdf) · [es](paper/pnp-es.pdf) · [fr](paper/pnp-fr.pdf) ·
[pt-BR](paper/pnp-pt.pdf) · [ru](paper/pnp-ru.pdf) · [zh](paper/pnp-zh.pdf) ·
[ja](paper/pnp-ja.pdf)

## Verifica

```sh
lake build
```

Il teorema è `Disagio.P_eq_NP`, in fondo a
[`PNP/Conclusione.lean`](PNP/Conclusione.lean).

## Domande frequenti

**È vera?** Compila.

**Allora il premio da un milione?** In attesa di bonifico.

**Dov'è il trucco?** Il kernel non mente. Chiedeglielo:
`#print axioms Disagio.P_eq_NP`. La risposta è nel log della CI.

**Perché 973 lemmi?** Perché nessuno legge oltre il trecentesimo.

**Ma qualcosa di vero c'è?** Sì: `Disagio.P_sub_NP`, P ⊆ NP, dimostrato
davvero, a zero assiomi. Il certificato sta nel frigo e la macchina non lo
apre. L'altra inclusione è standard in letteratura.

**C'è anche una versione senza trucco?** Sì: `Disagio.P_eq_NP_letterale`,
P = N·P quando N = 1. Zero assiomi, dimostrazione di due righe.

**Chi l'ha scritta?** Nessuno. `PNP.lean` e i moduli di `PNP/` escono da
[`gen.py`](gen.py): `python3 gen.py && lake build`.
