import IdealArithmetic.Examples.NF3_1_271660_2.PrimesBelow3_1_271660_2F0
import IdealArithmetic.Examples.NF3_1_271660_2.PrimesBelow3_1_271660_2F1
import IdealArithmetic.Examples.NF3_1_271660_2.PrimesBelow3_1_271660_2F2
import IdealArithmetic.Examples.NF3_1_271660_2.PrimesBelow3_1_271660_2F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 147]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 148 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB148I0
  exact PB148I1
  exact PB148I2
  exact PB148I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB148 : PrimesBelowBoundCertificate O 148 := by
  refine primesBelowBoundCertificate_of_Interval O eC 147 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 147 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 147 hC

lemma cert_eq_𝔭 : PB148.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 147 rfl rfl hel hC
