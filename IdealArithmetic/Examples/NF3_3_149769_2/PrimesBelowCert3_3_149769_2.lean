import IdealArithmetic.Examples.NF3_3_149769_2.PrimesBelow3_3_149769_2F0
import IdealArithmetic.Examples.NF3_3_149769_2.PrimesBelow3_3_149769_2F1
import IdealArithmetic.Examples.NF3_3_149769_2.PrimesBelow3_3_149769_2F2

noncomputable section
abbrev eC := ![1, 31, 79, 86]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 87 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB87I0
  exact PB87I1
  exact PB87I2

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB87 : PrimesBelowBoundCertificate O 87 := by
  refine primesBelowBoundCertificate_of_Interval O eC 86 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 86 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 86 hC

lemma cert_eq_𝔭 : PB87.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 86 rfl rfl hel hC
