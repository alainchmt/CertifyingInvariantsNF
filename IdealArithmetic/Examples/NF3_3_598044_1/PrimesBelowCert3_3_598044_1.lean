import IdealArithmetic.Examples.NF3_3_598044_1.PrimesBelow3_3_598044_1F0
import IdealArithmetic.Examples.NF3_3_598044_1.PrimesBelow3_3_598044_1F1
import IdealArithmetic.Examples.NF3_3_598044_1.PrimesBelow3_3_598044_1F2
import IdealArithmetic.Examples.NF3_3_598044_1.PrimesBelow3_3_598044_1F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 171]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 172 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB172I0
  exact PB172I1
  exact PB172I2
  exact PB172I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB172 : PrimesBelowBoundCertificate O 172 := by
  refine primesBelowBoundCertificate_of_Interval O eC 171 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 171 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 171 hC

lemma cert_eq_𝔭 : PB172.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 171 rfl rfl hel hC
