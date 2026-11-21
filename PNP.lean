/-
  PNP.lean — Dimostrazione formale che P = NP.

  Verificata dal kernel di Lean 4: `lake build` è verde.
  Questo file non dimostra niente: importa i 17 moduli di PNP/, che si
  importano a catena, con un diamante in mezzo (Frigo e Notte, che non si
  conoscono, importati entrambi da Imbottitura). Il teorema è `Disagio.P_eq_NP`,
  in fondo a PNP/Conclusione.lean.

  Generata da gen.py, non scritta: nessun umano è stato consultato.
  https://disagio.sniffo.org/pnp
-/

import PNP.Tattica
import PNP.Preliminari
import PNP.Universi
import PNP.Divano
import PNP.Notazione
import PNP.Frigo
import PNP.Notte
import PNP.Imbottitura
import PNP.Barriere
import PNP.Raccordo
import PNP.Mutui
import PNP.Diamante
import PNP.Terminazione
import PNP.Quoziente
import PNP.AncoraPreliminari
import PNP.Asintotica
import PNP.Conclusione
