import IdealArithmetic.Examples.NF3_1_196911_1.PrimesBelow3_1_196911_1F0
import IdealArithmetic.Examples.NF3_1_196911_1.PrimesBelow3_1_196911_1F1
import IdealArithmetic.Examples.NF3_1_196911_1.PrimesBelow3_1_196911_1F2

noncomputable section
abbrev eC := ![1, 31, 79, 125]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 126 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB126I0
  exact PB126I1
  exact PB126I2

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB126 : PrimesBelowBoundCertificate O 126 := by
  refine primesBelowBoundCertificate_of_Interval O eC 125 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 125 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 125 hC

lemma cert_eq_𝔭 : PB126.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 125 rfl rfl hel hC
