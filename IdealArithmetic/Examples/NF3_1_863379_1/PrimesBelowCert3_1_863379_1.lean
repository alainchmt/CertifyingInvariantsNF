import IdealArithmetic.Examples.NF3_1_863379_1.PrimesBelow3_1_863379_1F0
import IdealArithmetic.Examples.NF3_1_863379_1.PrimesBelow3_1_863379_1F1
import IdealArithmetic.Examples.NF3_1_863379_1.PrimesBelow3_1_863379_1F2
import IdealArithmetic.Examples.NF3_1_863379_1.PrimesBelow3_1_863379_1F3
import IdealArithmetic.Examples.NF3_1_863379_1.PrimesBelow3_1_863379_1F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 262]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 263 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB263I0
  exact PB263I1
  exact PB263I2
  exact PB263I3
  exact PB263I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB263 : PrimesBelowBoundCertificate O 263 := by
  refine primesBelowBoundCertificate_of_Interval O eC 262 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 262 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 262 hC

lemma cert_eq_𝔭 : PB263.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 262 rfl rfl hel hC
