
import IdealArithmetic.Examples.NF3_1_946067_1.RI3_1_946067_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-46954689, 956139, 593971]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-46954689, 956139, 593971]] 
 ![![2, 0, 0], ![0, 2, 0], ![1, 1, 1]] where
  M :=![![![-46954689, 956139, 593971], ![125327881, -23195849, 956139], ![201745329, 163573441, -23195849]]]
  hmulB := by decide  
  f := ![![![190824232263251, 59668168095611, 7345931706850]], ![![1549991590145350, 484661500537251, 59668168095611]], ![![7165399645291261, 2240523991301326, 275837800169856]]]
  g := ![![![-23774330, 181084, 593971], ![62185871, -12075994, 956139], ![112470589, 93384645, -23195849]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P0 : CertificateIrreducibleZModOfList' 2 2 2 1 [1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1], [0, 1]]
 g := ![![[1]], ![[1]]]
 h' := ![![[1, 1], [0, 1]], ![[0, 1], [1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], []]
 b := ![[], [1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P2P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2531, 1421, 361]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1446, 530, 361]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![190824232263251, 59668168095611, 7345931706850]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![190824232263251, 59668168095611, 7345931706850]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![190824232263251, 59668168095611, 7345931706850], ![1549991590145350, 484661500537251, 59668168095611], ![12589983468173921, 3936718313969790, 484661500537251]]]
  hmulB := by decide  
  f := ![![![-46954689, 956139, 593971]], ![![39186596, -11119855, 775055]], ![![77395320, 82264790, -11300939]]]
  g := ![![![61905066230395, 59668168095611, 7345931706850], ![502830960756244, 484661500537251, 59668168095611], ![4084301826833440, 3936718313969790, 484661500537251]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-46954689, 956139, 593971]] ![![190824232263251, 59668168095611, 7345931706850]]
  ![![2, 0, 0]] where
 M := ![![![2, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0)
instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0]] 
 ![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 3 2 1 [1, 1, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 2, 1], [2, 0, 2], [0, 1]]
 g := ![![[1]], ![[0, 0, 1, 1]], ![[2, 0, 2, 2]]]
 h' := ![![[2, 2, 1], [0, 1]], ![[2, 0, 2], [2, 2, 1]], ![[0, 1], [2, 0, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 2], []]
 b := ![[], [0, 0, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 3
  hpos := by decide
  P := [1, 1, 2, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-192825, -25530, -20910]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-64275, -8510, -6970]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 27 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def PBC3 : ContainsPrimesAboveP 3 ![I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![3, 0, 0]]) timesTableT_eq_Table B_one_repr 3 (by decide) 𝕀

instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-44914, -14044, -1729]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-44914, -14044, -1729]] 
 ![![5, 0, 0], ![0, 5, 0], ![1, 1, 1]] where
  M :=![![![-44914, -14044, -1729], ![-364819, -114074, -14044], ![-2963284, -926579, -114074]]]
  hmulB := by decide  
  f := ![![![-400, 33, 2]], ![![422, -320, 33]], ![![1397, 291, -57]]]
  g := ![![![-8637, -2463, -1729], ![-70155, -20006, -14044], ![-569842, -162501, -114074]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 4], [0, 1]]
 g := ![![[1, 1], [1]], ![[0, 4], [1]]]
 h' := ![![[4, 4], [4, 4], [0, 1]], ![[0, 1], [0, 1], [4, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [2, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1263, 1662, 352]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-323, 262, 352]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-400, 33, 2]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![-400, 33, 2]] 
 ![![5, 0, 0], ![4, 1, 0], ![4, 0, 1]] where
  M :=![![![-400, 33, 2], ![422, -320, 33], ![6963, 1742, -320]]]
  hmulB := by decide  
  f := ![![![-44914, -14044, -1729]], ![![-108895, -34050, -4192]], ![![-628588, -196551, -24198]]]
  g := ![![![-108, 33, 2], ![314, -320, 33], ![255, 1742, -320]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-44914, -14044, -1729]] ![![-400, 33, 2]]
  ![![5, 0, 0]] where
 M := ![![![5, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0]] 
 ![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [4, 3, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 2], [3, 4], [0, 1]]
 g := ![![[5, 5, 2], [1]], ![[5, 4, 1], [1]], ![[3, 5, 4], [1]]]
 h' := ![![[1, 2], [3, 4, 4], [0, 1]], ![[3, 4], [4, 3, 2], [1, 2]], ![[0, 1], [2, 0, 1], [3, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5], []]
 b := ![[], [2, 4, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [4, 3, 3, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-68782, -21483, -2233]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9826, -3069, -319]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def PBC7 : ContainsPrimesAboveP 7 ![I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![7, 0, 0]]) timesTableT_eq_Table B_one_repr 7 (by decide) 𝕀

instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5762115446490607731958, -1801735916711088509539, -221817250644099994856]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-5762115446490607731958, -1801735916711088509539, -221817250644099994856]] 
 ![![11, 0, 0], ![0, 11, 0], ![7, 5, 1]] where
  M :=![![![-5762115446490607731958, -1801735916711088509539, -221817250644099994856], ![-46803439885905098914616, -14634805472254607526198, -1801735916711088509539], ![-380166278426039675512729, -118872876554348639296176, -14634805472254607526198]]]
  hmulB := by decide  
  f := ![![![-195221282940, -1213187994, 3108294997]], ![![655850244367, -70889483060, -1213187994]], ![![150610870411, 22216635759, -5017941641]]]
  g := ![![![-382672244725627978906, -62968151226417139569, -221817250644099994856], ![-3108298951720679940713, -511465989881742270773, -1801735916711088509539], ![-25247512738205220257213, -4154440835734145605926, -14634805472254607526198]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [2, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 10], [0, 1]]
 g := ![![[8, 3], [5, 3], [1]], ![[4, 8], [1, 8], [1]]]
 h' := ![![[6, 10], [1, 6], [9, 6], [0, 1]], ![[0, 1], [4, 5], [1, 5], [6, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [1, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [2, 5, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8026, 1864, 408]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![470, -16, 408]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-195221282940, -1213187994, 3108294997]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-195221282940, -1213187994, 3108294997]] 
 ![![11, 0, 0], ![6, 1, 0], ![8, 0, 1]] where
  M :=![![![-195221282940, -1213187994, 3108294997], ![655850244367, -70889483060, -1213187994], ![-255982666734, 607322724607, -70889483060]]]
  hmulB := by decide  
  f := ![![![-5762115446490607731958, -1801735916711088509539, -221817250644099994856]], ![![-7397830233168067755124, -2313201906592830780312, -284785401870517134425]], ![![-38751200181633139760763, -12116978535276122488408, -1491758497946127953186]]]
  g := ![![![-19346228632, -1213187994, 3108294997], ![99172058789, -70889483060, -1213187994], ![-302982104536, 607322724607, -70889483060]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-5762115446490607731958, -1801735916711088509539, -221817250644099994856]] ![![-195221282940, -1213187994, 3108294997]]
  ![![11, 0, 0]] where
 M := ![![![11, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11172, -176, 191]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-11172, -176, 191]] 
 ![![13, 0, 0], ![0, 13, 0], ![11, 5, 1]] where
  M :=![![![-11172, -176, 191], ![40301, -3532, -176], ![-37136, 33261, -3532]]]
  hmulB := by decide  
  f := ![![![-1409920, -440863, -54276]], ![![-11452236, -3580960, -440863]], ![![-12753261, -3987773, -490947]]]
  g := ![![![-1021, -87, 191], ![3249, -204, -176], ![132, 3917, -3532]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [1, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 12], [0, 1]]
 g := ![![[7, 1], [3], [6, 1]], ![[0, 12], [3], [12, 12]]]
 h' := ![![[6, 12], [7, 1], [7, 9], [0, 1]], ![[0, 1], [0, 12], [9, 4], [6, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [1, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [1, 7, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1271, -14, 44]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-135, -18, 44]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1409920, 440863, 54276]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![1409920, 440863, 54276]] 
 ![![13, 0, 0], ![8, 1, 0], ![1, 0, 1]] where
  M :=![![![1409920, 440863, 54276], ![11452236, 3580960, 440863], ![93022093, 29086756, 3580960]]]
  hmulB := by decide  
  f := ![![![11172, 176, -191]], ![![3775, 380, -104]], ![![3716, -2545, 257]]]
  g := ![![![-167020, 440863, 54276], ![-1356639, 3580960, 440863], ![-11019455, 29086756, 3580960]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-11172, -176, 191]] ![![1409920, 440863, 54276]]
  ![![13, 0, 0]] where
 M := ![![![-13, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0)

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![617782164536947313, 193172164786745844, 23782019382830502]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![617782164536947313, 193172164786745844, 23782019382830502]] 
 ![![17, 0, 0], ![5, 1, 0], ![9, 0, 1]] where
  M :=![![![617782164536947313, 193172164786745844, 23782019382830502], ![5018006089777235922, 1569062939850167393, 193172164786745844], ![40759326770003373084, 12744892681247069682, 1569062939850167393]]]
  hmulB := by decide  
  f := ![![![-7371485159, -758024328, 205051050]], ![![376961515, -174092047, 15719466]], ![![-13310970567, 360151734, 157412723]]]
  g := ![![![-33065696108368025, 193172164786745844, 23782019382830502], ![-268579887797312567, 1569062939850167393, 193172164786745844], ![-2181570770287263639, 12744892681247069682, 1569062939850167393]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7397830233168067755124, 2313201906592830780312, 284785401870517134425]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![7397830233168067755124, 2313201906592830780312, 284785401870517134425]] 
 ![![17, 0, 0], ![6, 1, 0], ![15, 0, 1]] where
  M :=![![![7397830233168067755124, 2313201906592830780312, 284785401870517134425], ![60089719794679115363675, 18789246307988753132124, 2313201906592830780312], ![488085602291087294645832, 152617796058392346576155, 18789246307988753132124]]]
  hmulB := by decide  
  f := ![![![310018091016, -94319306813, 6913048644]], ![![195221282940, 1213187994, -3108294997]], ![![-897123668959, -219347565343, 40602103908]]]
  g := ![![![-632538954967451408419, 2313201906592830780312, 284785401870517134425], ![-5137869803067403831397, 18789246307988753132124, 2313201906592830780312], ![-41732933451711651870174, 152617796058392346576155, 18789246307988753132124]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![617782164536947313, 193172164786745844, 23782019382830502]] ![![7397830233168067755124, 2313201906592830780312, 284785401870517134425]]
  ![![27785570082657713971179032365413405366176, 8688173648917031164311786459149161474122, 1069627781766822429547081647004809819601]] where
 M := ![![![27785570082657713971179032365413405366176, 8688173648917031164311786459149161474122, 1069627781766822429547081647004809819601]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![27785570082657713971179032365413405366176, 8688173648917031164311786459149161474122, 1069627781766822429547081647004809819601]] ![![7397830233168067755124, 2313201906592830780312, 284785401870517134425]]
  ![![17, 0, 0]] where
 M := ![![![1249692770585173816645520918541138196377289419018248661758157206, 390762103003131545219756022504173201531512897282647022202636195, 48107924441160031243587853798196716000017871817187122953257388]]]
 hmul := by decide  
 g := ![![![![73511339446186695096795348149478717433958201118720509515185718, 22986006059007737954103295441421953031265464546038060129566835, 2829877908303531249622814929305689176471639518658066056073964]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8, 1, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-8, 1, 0]] 
 ![![19, 0, 0], ![11, 1, 0], ![12, 0, 1]] where
  M :=![![![-8, 1, 0], ![0, -8, 1], ![211, 40, -8]]]
  hmulB := by decide  
  f := ![![![24, 8, 1]], ![![25, 8, 1]], ![![104, 33, 4]]]
  g := ![![![-1, 1, 0], ![4, -8, 1], ![-7, 40, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![208, 65, 8]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![208, 65, 8]] 
 ![![19, 0, 0], ![16, 1, 0], ![10, 0, 1]] where
  M :=![![![208, 65, 8], ![1688, 528, 65], ![13715, 4288, 528]]]
  hmulB := by decide  
  f := ![![![64, -16, 1]], ![![65, -8, 0]], ![![-144, -31, 6]]]
  g := ![![![-48, 65, 8], ![-390, 528, 65], ![-3167, 4288, 528]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-8, 1, 0]] ![![-8, 1, 0]]
  ![![64, -16, 1]] where
 M := ![![![64, -16, 1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI19N1 : IdealMulLeCertificate' Table 
  ![![64, -16, 1]] ![![208, 65, 8]]
  ![![19, 0, 0]] where
 M := ![![![19, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2975, 446, -100]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![2975, 446, -100]] 
 ![![23, 0, 0], ![0, 23, 0], ![22, 19, 1]] where
  M :=![![![2975, 446, -100], ![-21100, -1025, 446], ![94106, -3260, -1025]]]
  hmulB := by decide  
  f := ![![![-108895, -34050, -4192]], ![![-884512, -276575, -34050]], ![![-1147216, -358719, -44163]]]
  g := ![![![225, 102, -100], ![-1344, -413, 446], ![5072, 705, -1025]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [18, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 22], [0, 1]]
 g := ![![[8, 9], [22, 4], [0, 13], [1]], ![[0, 14], [21, 19], [14, 10], [1]]]
 h' := ![![[17, 22], [18, 3], [0, 21], [5, 17], [0, 1]], ![[0, 1], [0, 20], [12, 2], [18, 6], [17, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [4, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [18, 6, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![862, 1010, 173]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-128, -99, 173]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-108895, -34050, -4192]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-108895, -34050, -4192]] 
 ![![23, 0, 0], ![4, 1, 0], ![7, 0, 1]] where
  M :=![![![-108895, -34050, -4192], ![-884512, -276575, -34050], ![-7184550, -2246512, -276575]]]
  hmulB := by decide  
  f := ![![![2975, 446, -100]], ![![-400, 33, 2]], ![![4997, -6, -75]]]
  g := ![![![2463, -34050, -4192], ![20006, -276575, -34050], ![162501, -2246512, -276575]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![2975, 446, -100]] ![![-108895, -34050, -4192]]
  ![![23, 0, 0]] where
 M := ![![![23, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0)

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6124929624933, -583134397120, 164625983032]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-6124929624933, -583134397120, 164625983032]] 
 ![![29, 0, 0], ![9, 1, 0], ![6, 0, 1]] where
  M :=![![![-6124929624933, -583134397120, 164625983032], ![34736082419752, 460109696347, -583134397120], ![-123041357792320, 11410706534952, 460109696347]]]
  hmulB := by decide  
  f := ![![![-6865676408645007273282649, -2146804570794513578255104, -264299714040825969910296]], ![![-4053735425531701555538493, -1267548486463057526689325, -156051793005584389911992]], ![![-17040338720328014091431822, -5328284479971100146579560, -655981491535275927212285]]]
  g := ![![![-64292274105, -583134397120, 164625983032], ![1175651777081, 460109696347, -583134397120], ![-7879254302930, 11410706534952, 460109696347]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15250576, 955062, -348731]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![15250576, 955062, -348731]] 
 ![![29, 0, 0], ![11, 1, 0], ![24, 0, 1]] where
  M :=![![![15250576, 955062, -348731], ![-73582241, 1301336, 955062], ![201518082, -35379761, 1301336]]]
  hmulB := by decide  
  f := ![![![35483340685078, 11095162870459, 1365959628460]], ![![23397732039342, 7316155772363, 900714440811]], ![![110092398003749, 34424410528084, 4238095065742]]]
  g := ![![![452222, 955062, -348731], ![-3821325, 1301336, 955062], ![19291841, -35379761, 1301336]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-6124929624933, -583134397120, 164625983032]] ![![-6124929624933, -583134397120, 164625983032]]
  ![![-2996846049923526544573991, 5181850134255498031006784, -592530824338228423458352]] where
 M := ![![![-2996846049923526544573991, 5181850134255498031006784, -592530824338228423458352]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI29N1 : IdealMulLeCertificate' Table 
  ![![-2996846049923526544573991, 5181850134255498031006784, -592530824338228423458352]] ![![15250576, 955062, -348731]]
  ![![29, 0, 0]] where
 M := ![![![-546401449095847658621820592212624, 24844753294398954462327606484854, 5222999579937192972235635637757]]]
 hmul := by decide  
 g := ![![![![-18841429279167160642131744559056, 856715630841343257321641602926, 180103433790937688697780539233]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2710945, 847676, 104360]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![2710945, 847676, 104360]] 
 ![![31, 0, 0], ![0, 31, 0], ![24, 23, 1]] where
  M :=![![![2710945, 847676, 104360], ![22019960, 6885345, 847676], ![178859636, 55927000, 6885345]]]
  hmulB := by decide  
  f := ![![![3775, 380, -104]], ![![-21944, -385, 380]], ![![-10772, -209, 189]]]
  g := ![![![6655, -50084, 104360], ![54056, -406813, 847676], ![439076, -3304385, 6885345]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [28, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 30], [0, 1]]
 g := ![![[6, 10], [9, 20], [1, 10], [18, 1]], ![[0, 21], [28, 11], [26, 21], [5, 30]]]
 h' := ![![[18, 30], [27, 14], [3, 19], [23, 17], [0, 1]], ![[0, 1], [0, 17], [4, 12], [19, 14], [18, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [15, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [28, 13, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8382, -926, 294]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-498, -248, 294]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3775, 380, -104]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![3775, 380, -104]] 
 ![![31, 0, 0], ![8, 1, 0], ![29, 0, 1]] where
  M :=![![![3775, 380, -104], ![-21944, -385, 380], ![80180, -6744, -385]]]
  hmulB := by decide  
  f := ![![![2710945, 847676, 104360]], ![![1409920, 440863, 54276]], ![![8305711, 2597084, 319735]]]
  g := ![![![121, 380, -104], ![-964, -385, 380], ![4687, -6744, -385]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![2710945, 847676, 104360]] ![![3775, 380, -104]]
  ![![31, 0, 0]] where
 M := ![![![31, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)


lemma PB276I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB276I0 : PrimesBelowBoundCertificateInterval O 1 31 276 where
  m := 11
  g := ![2, 1, 2, 1, 2, 2, 3, 3, 2, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB276I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0]
    · exact ![I5N0, I5N1]
    · exact ![I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1, I17N1]
    · exact ![I19N0, I19N0, I19N1]
    · exact ![I23N0, I23N1]
    · exact ![I29N0, I29N0, I29N1]
    · exact ![I31N0, I31N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
    · exact PBC29
    · exact PBC31
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![4, 2]
    · exact ![27]
    · exact ![25, 5]
    · exact ![343]
    · exact ![121, 11]
    · exact ![169, 13]
    · exact ![17, 17, 17]
    · exact ![19, 19, 19]
    · exact ![529, 23]
    · exact ![29, 29, 29]
    · exact ![961, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I5N0, I5N1, I11N0, I11N1, I13N0, I13N1, I17N0, I17N1, I19N0, I19N1, I23N1, I29N0, I29N1, I31N1]
  Il := ![[I2N0, I2N1], [I3N0], [I5N0, I5N1], [], [I11N0, I11N1], [I13N0, I13N1], [I17N0, I17N1, I17N1], [I19N0, I19N0, I19N1], [I23N1], [I29N0, I29N0, I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
