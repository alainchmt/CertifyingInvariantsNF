import IdealArithmetic.Examples.NF3_1_735727_1.PrimesBelow3_1_735727_1F0
import IdealArithmetic.Examples.NF3_1_735727_1.PrimesBelow3_1_735727_1F1
import IdealArithmetic.Examples.NF3_1_735727_1.PrimesBelow3_1_735727_1F2
import IdealArithmetic.Examples.NF3_1_735727_1.PrimesBelow3_1_735727_1F3
import IdealArithmetic.Examples.NF3_1_735727_1.PrimesBelow3_1_735727_1F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 242]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 243 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB243I0
  exact PB243I1
  exact PB243I2
  exact PB243I3
  exact PB243I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB243 : PrimesBelowBoundCertificate O 243 := by
  refine primesBelowBoundCertificate_of_Interval O eC 242 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 242 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 242 hC

lemma cert_eq_𝔭 : PB243.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 242 rfl rfl hel hC
