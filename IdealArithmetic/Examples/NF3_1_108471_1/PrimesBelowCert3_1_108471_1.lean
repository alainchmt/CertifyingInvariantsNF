import IdealArithmetic.Examples.NF3_1_108471_1.PrimesBelow3_1_108471_1F0
import IdealArithmetic.Examples.NF3_1_108471_1.PrimesBelow3_1_108471_1F1
import IdealArithmetic.Examples.NF3_1_108471_1.PrimesBelow3_1_108471_1F2

noncomputable section
abbrev eC := ![1, 31, 79, 93]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 94 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB94I0
  exact PB94I1
  exact PB94I2

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB94 : PrimesBelowBoundCertificate O 94 := by
  refine primesBelowBoundCertificate_of_Interval O eC 93 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 93 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 93 hC

lemma cert_eq_𝔭 : PB94.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 93 rfl rfl hel hC
