
import IdealArithmetic.Examples.NF3_1_87843_1.RI3_1_87843_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4094, 3288, 373]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-4094, 3288, 373]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-4094, 3288, 373], ![11190, -14165, 3661], ![109830, -87657, -10504]]]
  hmulB := by decide  
  f := ![![![469701437, 1841091, 17320913]], ![![259813695, 1018393, 9581002]], ![![287430060, 1126641, 10599395]]]
  g := ![![![-2047, 3288, 373], ![5595, -14165, 3661], ![54915, -87657, -10504]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![469701437, 1841091, 17320913]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![469701437, 1841091, 17320913]] 
 ![![2, 0, 0], ![0, 2, 0], ![1, 1, 1]] where
  M :=![![![469701437, 1841091, 17320913], ![519627390, 2036786, 19162004], ![574860120, 2253282, 21198790]]]
  hmulB := by decide  
  f := ![![![-4094, 3288, 373]], ![![11190, -14165, 3661]], ![![58463, -49267, -3235]]]
  g := ![![![226190262, -7739911, 17320913], ![250232693, -8562609, 19162004], ![276830665, -9472754, 21198790]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P1 : CertificateIrreducibleZModOfList' 2 2 2 1 [1, 1, 1] where
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

def PI2N1 : CertifiedPrimeIdeal' SI2N1 2 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P2P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-89, 353, -245]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![78, 299, -245]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N1 B_one_repr
lemma NI2N1 : Nat.card (O ⧸ I2N1) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-4094, 3288, 373]] ![![469701437, 1841091, 17320913]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11079801207, 9692896144, 291382578]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-11079801207, 9692896144, 291382578]] 
 ![![3, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-11079801207, 9692896144, 291382578], ![8741477340, -18947130813, 9984278722], ![299528361660, -260834048154, -8962852091]]]
  hmulB := by decide  
  f := ![![![2774060167982853159171, 10873497090807576092, 102297440547090223882]], ![![1022974405470902238820, 4009757737139038119, 37723645879299266658]], ![![1131709376378977999740, 4435966729822039054, 41733403616438304777]]]
  g := ![![![-3693267069, 9692896144, 291382578], ![2913825780, -18947130813, 9984278722], ![99842787220, -260834048154, -8962852091]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 1, 0]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-1, 1, 0]] 
 ![![3, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![-1, 1, 0], ![0, -1, 1], ![30, -27, 0]]]
  hmulB := by decide  
  f := ![![![27, 0, 1]], ![![28, 0, 1]], ![![28, 1, 1]]]
  g := ![![![-1, 1, 0], ![0, -1, 1], ![28, -27, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-11079801207, 9692896144, 291382578]] ![![-11079801207, 9692896144, 291382578]]
  ![![294769572992995193289, -367050430974096791892, 90936496737163605724]] where
 M := ![![![294769572992995193289, -367050430974096791892, 90936496737163605724]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![294769572992995193289, -367050430974096791892, 90936496737163605724]] ![![-1, 1, 0]]
  ![![3, 0, 0]] where
 M := ![![![2433325329121912978431, -1793465407936325369367, -367050430974096791892]]]
 hmul := by decide  
 g := ![![![![811108443040637659477, -597821802645441789789, -122350143658032263964]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1613285, -618138, -759421]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![1613285, -618138, -759421]] 
 ![![5, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![1613285, -618138, -759421], ![-22782630, 22117652, -1377559], ![-41326770, 14411463, 20740093]]]
  hmulB := by decide  
  f := ![![![-478574799980453, -1875871963911, -17648130964634]], ![![-105888785787804, -415052787067, -3904800585709]], ![![-117144017571270, -459169973661, -4319853372776]]]
  g := ![![![322657, -618138, -759421], ![-4556526, 22117652, -1377559], ![-8265354, 14411463, 20740093]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-478574799980453, -1875871963911, -17648130964634]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![-478574799980453, -1875871963911, -17648130964634]] 
 ![![5, 0, 0], ![0, 5, 0], ![2, 4, 1]] where
  M :=![![![-478574799980453, -1875871963911, -17648130964634], ![-529443928939020, -2075263935335, -19524002928545], ![-585720087856350, -2295849868305, -21599266863880]]]
  hmulB := by decide  
  f := ![![![1613285, -618138, -759421]], ![![-22782630, 22117652, -1377559]], ![![-25846144, 20329159, 2742203]]]
  g := ![![![-88655707610237, 13743330378925, -17648130964634], ![-98079184616386, 15204149555769, -19524002928545], ![-108504310825718, 16820243517443, -21599266863880]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P1 : CertificateIrreducibleZModOfList' 5 2 2 2 [3, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 4], [0, 1]]
 g := ![![[1, 4], [1]], ![[4, 1], [1]]]
 h' := ![![[2, 4], [2, 2], [0, 1]], ![[0, 1], [1, 3], [2, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [1, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N1 : CertifiedPrimeIdeal' SI5N1 5 where
  n := 2
  hpos := by decide
  P := [3, 3, 1]
  hirr := P5P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![97, 194, -254]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![121, 242, -254]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N1 B_one_repr
lemma NI5N1 : Nat.card (O ⧸ I5N1) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![1613285, -618138, -759421]] ![![-478574799980453, -1875871963911, -17648130964634]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![60150259549, 235771264, 2218126943]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![60150259549, 235771264, 2218126943]] 
 ![![7, 0, 0], ![3, 1, 0], ![5, 0, 1]] where
  M :=![![![60150259549, 235771264, 2218126943], ![66543808290, 260832088, 2453898207], ![73616946210, 288556701, 2714730295]]]
  hmulB := by decide  
  f := ![![![-29147, 52163, -23336]], ![![-112503, 108202, -5883]], ![![102725, -173942, 73296]]]
  g := ![![![6907473006, 235771264, 2218126943], ![7641688713, 260832088, 2453898207], ![8453946376, 288556701, 2714730295]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-51730718303416397, -202769147356526, -1907644304611464]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-51730718303416397, -202769147356526, -1907644304611464]] 
 ![![7, 0, 0], ![5, 1, 0], ![3, 0, 1]] where
  M :=![![![-51730718303416397, -202769147356526, -1907644304611464], ![-57229329138343920, -224322078906869, -2110413451967990], ![-63312403559039700, -248165935208190, -2334735530874859]]]
  hmulB := by decide  
  f := ![![![-88668371, 62289674, 16143476]], ![![5851775, -30441979, 22735790]], ![![298141341, -206645964, -56811235]]]
  g := ![![![-6427705664685625, -202769147356526, -1907644304611464], ![-7110925483986515, -224322078906869, -2110413451967990], ![-7866766755767739, -248165935208190, -2334735530874859]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![60150259549, 235771264, 2218126943]] ![![-51730718303416397, -202769147356526, -1907644304611464]]
  ![![-3265544112035915639634176933, -12799969089331524934642360, -120421614682497206599935133]] where
 M := ![![![-3265544112035915639634176933, -12799969089331524934642360, -120421614682497206599935133]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![-3265544112035915639634176933, -12799969089331524934642360, -120421614682497206599935133]] ![![-51730718303416397, -202769147356526, -1907644304611464]]
  ![![7, 0, 0]] where
 M := ![![![177285658077093412210708579056513220723601701, 694907453555671161544129253818013828924868, 6537662476218262521967910420257968954737559]]]
 hmul := by decide  
 g := ![![![![25326522582441916030101225579501888674800243, 99272493365095880220589893402573404132124, 933951782316894645995415774322566993533937]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0]] 
 ![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [10, 6, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 2, 3], [4, 8, 8], [0, 1]]
 g := ![![[4, 6, 1], [3, 8, 1], []], ![[3, 10, 3, 9], [2, 0, 1, 5], [7, 9]], ![[0, 1, 1, 2], [2, 1, 7, 10], [2, 9]]]
 h' := ![![[4, 2, 3], [3, 1, 10], [0, 0, 1], [0, 1]], ![[4, 8, 8], [6, 8, 6], [1, 5, 8], [4, 2, 3]], ![[0, 1], [0, 2, 6], [7, 6, 2], [4, 8, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 1], []]
 b := ![[], [6, 0, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [10, 6, 3, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3190, -2178, -638]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![290, -198, -58]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def PBC11 : ContainsPrimesAboveP 11 ![I11N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![11, 0, 0]]) timesTableT_eq_Table B_one_repr 11 (by decide) 𝕀

instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, 22, -6]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-17, 22, -6]] 
 ![![13, 0, 0], ![0, 13, 0], ![5, 5, 1]] where
  M :=![![![-17, 22, -6], ![-180, 145, 16], ![480, -612, 161]]]
  hmulB := by decide  
  f := ![![![-2549, -10, -94]], ![![-2820, -11, -104]], ![![-2305, -9, -85]]]
  g := ![![![1, 4, -6], ![-20, 5, 16], ![-25, -109, 161]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [2, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 12], [0, 1]]
 g := ![![[], [4], [0, 1]], ![[], [4], [0, 12]]]
 h' := ![![[0, 12], [5], [0, 11], [0, 1]], ![[0, 1], [5], [0, 2], [0, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [0, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [2, 0, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1173, -985, 375]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-54, -220, 375]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2549, 10, 94]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![2549, 10, 94]] 
 ![![13, 0, 0], ![7, 1, 0], ![3, 0, 1]] where
  M :=![![![2549, 10, 94], ![2820, 11, 104], ![3120, 12, 115]]]
  hmulB := by decide  
  f := ![![![17, -22, 6]], ![![23, -23, 2]], ![![-33, 42, -11]]]
  g := ![![![169, 10, 94], ![187, 11, 104], ![207, 12, 115]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-17, 22, -6]] ![![2549, 10, 94]]
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
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0]] 
 ![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [13, 6, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 14, 16], [2, 2, 1], [0, 1]]
 g := ![![[0, 14, 9], [6, 4], [2, 1], []], ![[9, 8, 0, 16], [10, 16], [2, 4], [8, 1]], ![[13, 16, 16, 16], [16, 4], [9, 9], [6, 1]]]
 h' := ![![[0, 14, 16], [3, 5, 3], [8, 9, 15], [0, 0, 1], [0, 1]], ![[2, 2, 1], [14, 6, 1], [12, 10, 4], [15, 7, 2], [0, 14, 16]], ![[0, 1], [12, 6, 13], [4, 15, 15], [11, 10, 14], [2, 2, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 7], []]
 b := ![[], [16, 13, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [13, 6, 15, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8109, 7854, -442]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-477, 462, -26]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def PBC17 : ContainsPrimesAboveP 17 ![I17N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![17, 0, 0]]) timesTableT_eq_Table B_one_repr 17 (by decide) 𝕀

instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-942493991429, -3694298268, -34755815381]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-942493991429, -3694298268, -34755815381]] 
 ![![19, 0, 0], ![0, 19, 0], ![3, 9, 1]] where
  M :=![![![-942493991429, -3694298268, -34755815381], ![-1042674461430, -4086976142, -38450113649], ![-1153503409470, -4521392907, -42537089791]]]
  hmulB := by decide  
  f := ![![![195859, -164241, -11570]], ![![-347100, 508249, -175811]], ![![-411087, 446385, -67609]]]
  g := ![![![-44117186594, 16268844219, -34755815381], ![-48806532657, 17998107721, -38450113649], ![-53994323163, 19911179748, -42537089791]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [4, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 18], [0, 1]]
 g := ![![[17, 5], [1, 7], [7], [1]], ![[0, 14], [0, 12], [7], [1]]]
 h' := ![![[8, 18], [15, 10], [7, 11], [15, 8], [0, 1]], ![[0, 1], [0, 9], [0, 8], [3, 11], [8, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [16, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [4, 11, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![244, -85, -77]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![25, 32, -77]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![195859, -164241, -11570]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![195859, -164241, -11570]] 
 ![![19, 0, 0], ![9, 1, 0], ![14, 0, 1]] where
  M :=![![![195859, -164241, -11570], ![-347100, 508249, -175811], ![-5274330, 4399797, 332438]]]
  hmulB := by decide  
  f := ![![![-942493991429, -3694298268, -34755815381]], ![![-501322125489, -1965034766, -18486971162]], ![![-755179962604, -2960082561, -27848342375]]]
  g := ![![![96632, -164241, -11570], ![-129473, 508249, -175811], ![-2606665, 4399797, 332438]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-942493991429, -3694298268, -34755815381]] ![![195859, -164241, -11570]]
  ![![19, 0, 0]] where
 M := ![![![19, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16207374497, 7045754324, 6873776809]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-16207374497, 7045754324, 6873776809]] 
 ![![23, 0, 0], ![0, 23, 0], ![10, 2, 1]] where
  M :=![![![-16207374497, 7045754324, 6873776809], ![206213304270, -201799348340, 13919531133], ![417585933990, -169614036321, -187879817207]]]
  hmulB := by decide  
  f := ![![![1751085762511950920351, 6863739353668537973, 64573794667790957224]], ![![1937213840033728716720, 7593306481595075303, 71437534021459495197]], ![![1022974405470902238820, 4009757737139038119, 37723645879299266658]]]
  g := ![![![-3693267069, -291382578, 6873776809], ![2913825780, -9984278722, 13919531133], ![99842787220, 8962852091, -187879817207]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [9, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 22], [0, 1]]
 g := ![![[6, 18], [21, 6], [0, 18], [1]], ![[0, 5], [19, 17], [17, 5], [1]]]
 h' := ![![[15, 22], [18, 8], [0, 11], [14, 15], [0, 1]], ![[0, 1], [0, 15], [4, 12], [9, 8], [15, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [3, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [9, 8, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1051, 972, -20]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-37, 44, -20]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1751085762511950920351, -6863739353668537973, -64573794667790957224]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-1751085762511950920351, -6863739353668537973, -64573794667790957224]] 
 ![![23, 0, 0], ![20, 1, 0], ![14, 0, 1]] where
  M :=![![![-1751085762511950920351, -6863739353668537973, -64573794667790957224], ![-1937213840033728716720, -7593306481595075303, -71437534021459495197], ![-2143126020643784855910, -8400421454322346401, -79030840503054570500]]]
  hmulB := by decide  
  f := ![![![16207374497, -7045754324, -6873776809]], ![![5127573290, 2647141820, -6582394231]], ![![-8290551784, 3085803295, 3984649647]]]
  g := ![![![-30859906525630728685, -6863739353668537973, -64573794667790957224], ![-34140097134843229474, -7593306481595075303, -71437534021459495197], ![-37768948891937997430, -8400421454322346401, -79030840503054570500]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-16207374497, 7045754324, 6873776809]] ![![-1751085762511950920351, -6863739353668537973, -64573794667790957224]]
  ![![23, 0, 0]] where
 M := ![![![-23, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-277, 288, -34]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-277, 288, -34]] 
 ![![29, 0, 0], ![0, 29, 0], ![9, 12, 1]] where
  M :=![![![-277, 288, -34], ![-1020, 641, 254], ![7620, -7878, 895]]]
  hmulB := by decide  
  f := ![![![88783, 348, 3274]], ![![98220, 385, 3622]], ![![71943, 282, 2653]]]
  g := ![![![1, 24, -34], ![-114, -83, 254], ![-15, -642, 895]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [15, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 28], [0, 1]]
 g := ![![[20, 5], [22], [27, 4], [19, 1]], ![[28, 24], [22], [16, 25], [9, 28]]]
 h' := ![![[19, 28], [19, 11], [1, 14], [5, 27], [0, 1]], ![[0, 1], [25, 18], [6, 15], [25, 2], [19, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [7, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [15, 10, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![284, 21, 9]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7, -3, 9]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-88783, -348, -3274]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-88783, -348, -3274]] 
 ![![29, 0, 0], ![16, 1, 0], ![5, 0, 1]] where
  M :=![![![-88783, -348, -3274], ![-98220, -385, -3622], ![-108660, -426, -4007]]]
  hmulB := by decide  
  f := ![![![277, -288, 34]], ![![188, -181, 10]], ![![-215, 222, -25]]]
  g := ![![![-2305, -348, -3274], ![-2550, -385, -3622], ![-2821, -426, -4007]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-277, 288, -34]] ![![-88783, -348, -3274]]
  ![![29, 0, 0]] where
 M := ![![![-29, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4753844219, -1772994086, 5486871746]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-4753844219, -1772994086, 5486871746]] 
 ![![31, 0, 0], ![0, 31, 0], ![20, 16, 1]] where
  M :=![![![-4753844219, -1772994086, 5486871746], ![164606152380, -152899381361, 3713877660], ![111416329800, 64331455560, -149185503701]]]
  hmulB := by decide  
  f := ![![![728111357041048681531, 2853981616529499854, 26850148788491690566]], ![![805504463654750716980, 3157339751773036249, 29704130405021190420]], ![![914239434562826477900, 3583548744456037184, 33713888142160228539]]]
  g := ![![![-3693267069, -2889127162, 5486871746], ![2913825780, -6849078191, 3713877660], ![99842787220, 79074177896, -149185503701]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [2, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 30], [0, 1]]
 g := ![![[13, 16], [10, 8], [15, 2], [5, 1]], ![[0, 15], [19, 23], [25, 29], [10, 30]]]
 h' := ![![[5, 30], [11, 4], [1, 16], [21, 23], [0, 1]], ![[0, 1], [0, 27], [19, 15], [12, 8], [5, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [24, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [2, 26, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![299, -325, -30]
  a := ![1, -4, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![29, 5, -30]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![728111357041048681531, 2853981616529499854, 26850148788491690566]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![728111357041048681531, 2853981616529499854, 26850148788491690566]] 
 ![![31, 0, 0], ![14, 1, 0], ![21, 0, 1]] where
  M :=![![![728111357041048681531, 2853981616529499854, 26850148788491690566], ![805504463654750716980, 3157339751773036249, 29704130405021190420], ![891123912150635712600, 3492942719178575640, 32861470156794226669]]]
  hmulB := by decide  
  f := ![![![-4753844219, -1772994086, 5486871746]], ![![3162978494, -5732945115, 2597744584]], ![![373729071, 874147734, -1095522485]]]
  g := ![![![4009757737139038119, 2853981616529499854, 26850148788491690566], ![4435966729822039054, 3157339751773036249, 29704130405021190420], ![4907478735143770761, 3492942719178575640, 32861470156794226669]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-4753844219, -1772994086, 5486871746]] ![![728111357041048681531, 2853981616529499854, 26850148788491690566]]
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


lemma PB84I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB84I0 : PrimesBelowBoundCertificateInterval O 1 31 84 where
  m := 11
  g := ![2, 3, 2, 3, 1, 2, 1, 2, 2, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB84I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N0, I3N1]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N1, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N1]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1]
    · exact ![I29N0, I29N1]
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
    · exact ![2, 4]
    · exact ![3, 3, 3]
    · exact ![5, 25]
    · exact ![7, 7, 7]
    · exact ![1331]
    · exact ![169, 13]
    · exact ![4913]
    · exact ![361, 19]
    · exact ![529, 23]
    · exact ![841, 29]
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
      exact NI3N0
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I5N1, I7N0, I7N1, I13N1, I19N1, I23N1, I29N1, I31N1]
  Il := ![[I2N0, I2N1], [I3N0, I3N0, I3N1], [I5N0, I5N1], [I7N0, I7N1, I7N1], [], [I13N1], [], [I19N1], [I23N1], [I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
