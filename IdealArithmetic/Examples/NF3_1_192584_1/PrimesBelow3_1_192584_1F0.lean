
import IdealArithmetic.Examples.NF3_1_192584_1.RI3_1_192584_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2108871139, 430434254, 39973233]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2108871139, 430434254, 39973233]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![2108871139, 430434254, 39973233], ![-3526915813, 2788416100, 900841741], ![-44251893699, 5678479765, 3218850354]]]
  hmulB := by decide  
  f := ![![![3860082552848428535, -1158516256129495671, 276291136293144914]], ![![-12325628098151206811, 3699257806851198201, -882225119836350757]], ![![53612627660824779245, -16090614599174931776, 3837403374997770658]]]
  g := ![![![819231826, 430434254, 39973233], ![-3608086827, 2788416100, 900841741], ![-26574611909, 5678479765, 3218850354]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12, 2, 1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-12, 2, 1]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![-12, 2, 1], ![-97, 5, 5], ![-239, -7, 7]]]
  hmulB := by decide  
  f := ![![![70, -21, 5]], ![![-223, 67, -16]], ![![937, -281, 67]]]
  g := ![![![-7, 2, 1], ![-51, 5, 5], ![-116, -7, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2108871139, 430434254, 39973233]] ![![2108871139, 430434254, 39973233]]
  ![![1160340846496339952, 2334947374074814951, 600719395358193083]] where
 M := ![![![1160340846496339952, 2334947374074814951, 600719395358193083]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![1160340846496339952, 2334947374074814951, 600719395358193083]] ![![-12, 2, 1]]
  ![![2, 0, 0]] where
 M := ![![![-383985920933821276508, 9790382795859403078, 17040113484377766288]]]
 hmul := by decide  
 g := ![![![![-191992960466910638254, 4895191397929701539, 8520056742188883144]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)
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


def P3P0 : CertificateIrreducibleZModOfList' 3 3 2 1 [1, 2, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 1], [1, 1], [0, 1]]
 g := ![![[1]], ![[1]], ![[1]]]
 h' := ![![[2, 1], [0, 1]], ![[1, 1], [2, 1]], ![[0, 1], [1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], []]
 b := ![[], [2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 3
  hpos := by decide
  P := [1, 2, 0, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3843, 8916, -1320]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1281, 2972, -440]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0]] 
 ![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [3, 4, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 0, 4], [0, 4, 1], [0, 1]]
 g := ![![[2, 4, 1], []], ![[3, 2, 3, 4], [4, 1]], ![[0, 1], [2, 1]]]
 h' := ![![[4, 0, 4], [0, 0, 1], [0, 1]], ![[0, 4, 1], [4, 1, 4], [4, 0, 4]], ![[0, 1], [4, 4], [0, 4, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 3], []]
 b := ![[], [4, 0, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [3, 4, 1, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![682250, -226245, 40700]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![136450, -45249, 8140]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 125 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def PBC5 : ContainsPrimesAboveP 5 ![I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![5, 0, 0]]) timesTableT_eq_Table B_one_repr 5 (by decide) 𝕀


def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13718959, -2085498, -1087568]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![13718959, -2085498, -1087568]] 
 ![![7, 0, 0], ![4, 1, 0], ![3, 0, 1]] where
  M :=![![![13718959, -2085498, -1087568], ![105583734, -4769697, -5258564], ![251054590, 9136822, -6855195]]]
  hmulB := by decide  
  f := ![![![-80743766269523, 24233410691006, -5779354877976]], ![![39059211218934, -11722736633013, 2795720998876]], ![![-343483629603021, 103088823402448, -24585350448291]]]
  g := ![![![3617665, -2085498, -1087568], ![20062602, -4769697, -5258564], ![33581841, 9136822, -6855195]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3206202, 120607, 153000]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-3206202, 120607, 153000]] 
 ![![7, 0, 0], ![5, 1, 0], ![2, 0, 1]] where
  M :=![![![-3206202, 120607, 153000], ![-15026393, -605202, 394214], ![-18213093, -4222681, -484595]]]
  hmulB := by decide  
  f := ![![![-1957917830924, 587624643835, -140140873898]], ![![667426000731, -200312781145, 47772006326]], ![![-8049271367385, 2415806294669, -576138541593]]]
  g := ![![![-587891, 120607, 153000], ![-1826973, -605202, 394214], ![552786, -4222681, -484595]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![13718959, -2085498, -1087568]] ![![13718959, -2085498, -1087568]]
  ![![-305023768382971, -28600583231372, 3501914618920]] where
 M := ![![![-305023768382971, -28600583231372, 3501914618920]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![-305023768382971, -28600583231372, 3501914618920]] ![![-3206202, 120607, 153000]]
  ![![7, 0, 0]] where
 M := ![![![1343950723268374467778, -34266339785507910773, -59640397195322182008]]]
 hmul := by decide  
 g := ![![![![191992960466910638254, -4895191397929701539, -8520056742188883144]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N0
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


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [1, 3, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 8, 1], [2, 2, 10], [0, 1]]
 g := ![![[9, 2, 3], [2, 4, 1], []], ![[5, 10, 0, 4], [3, 2, 9, 4], [9, 1]], ![[8, 5, 4, 2], [8, 10, 2, 2], [0, 1]]]
 h' := ![![[2, 8, 1], [9, 1, 6], [0, 0, 1], [0, 1]], ![[2, 2, 10], [3, 10, 2], [6, 4, 2], [2, 8, 1]], ![[0, 1], [2, 0, 3], [4, 7, 8], [2, 2, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 3], []]
 b := ![[], [8, 4, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [1, 3, 7, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-958200914, 438036247, -75042044]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-87109174, 39821477, -6822004]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![129935717923368606234, -38997259619486194277, 9300341808395188084]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![129935717923368606234, -38997259619486194277, 9300341808395188084]] 
 ![![13, 0, 0], ![0, 13, 0], ![11, 9, 1]] where
  M :=![![![129935717923368606234, -38997259619486194277, 9300341808395188084], ![-959731098650609814593, 288041528666086803662, -68694177430577200470], ![3479414688184930521979, -1044267427675468014153, 249044269046600609385]]]
  hmulB := by decide  
  f := ![![![-5617591080, -2900727939, -590327186]], ![![55541663475, -15653153242, -6391783064]], ![![57650534614, -15222718988, -6351809831]]]
  g := ![![![2125535233155502870, -9438487376541760541, 9300341808395188084], ![-15699626685712354571, 69714548118560123684, -68694177430577200470], ![56917517590178755288, -252743526853451807586, 249044269046600609385]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [7, 7, 1] where
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
 g := ![![[1, 9], [9], [6, 1]], ![[3, 4], [9], [12, 12]]]
 h' := ![![[6, 12], [11, 10], [10, 3], [0, 1]], ![[0, 1], [6, 3], [2, 10], [6, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [4, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [7, 7, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-37, -1192, 402]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-343, -370, 402]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![133795800476217034769, -40155775875615689948, 9576632944688332998]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![133795800476217034769, -40155775875615689948, 9576632944688332998]] 
 ![![13, 0, 0], ![7, 1, 0], ![2, 0, 1]] where
  M :=![![![133795800476217034769, -40155775875615689948, 9576632944688332998], ![-988242437399760656750, 296598560535918695735, -70734918806543046898], ![3582779860953731651934, -1075290140617688382034, 256442784660303005787]]]
  hmulB := by decide  
  f := ![![![70994587913, -8990828856, -5131182226]], ![![76612178993, -6090100917, -4540855040]], ![![95573823372, 3042517154, -2729900249]]]
  g := ![![![30440997362780784493, -40155775875615689948, 9576632944688332998], ![-224843271041392725623, 296598560535918695735, -70734918806543046898], ![815148098150534178046, -1075290140617688382034, 256442784660303005787]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![129935717923368606234, -38997259619486194277, 9300341808395188084]] ![![133795800476217034769, -40155775875615689948, 9576632944688332998]]
  ![![13, 0, 0]] where
 M := ![![![89244677619385632247843586284121411924152, -26784766486094952021469359163352781727283, 6387820221456198108064194109914486354386]]]
 hmul := by decide  
 g := ![![![![6864975201491202480603352791086262455704, -2060366652776534770882258397180983209791, 491370786265861392928014931531883565722]]]]
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


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [13, 8, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 6, 8], [12, 10, 9], [0, 1]]
 g := ![![[13, 10, 16], [14, 13], [13, 1], []], ![[12, 4, 13, 13], [7, 2], [11, 15], [10, 13]], ![[12, 11, 3, 9], [4, 4], [14, 2], [9, 13]]]
 h' := ![![[1, 6, 8], [6, 12, 13], [1, 2, 8], [0, 0, 1], [0, 1]], ![[12, 10, 9], [7, 0, 5], [8, 3, 11], [7, 1, 10], [1, 6, 8]], ![[0, 1], [8, 5, 16], [3, 12, 15], [10, 16, 6], [12, 10, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 11], []]
 b := ![[], [15, 9, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [13, 8, 4, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6069, 8534, -1020]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-357, 502, -60]
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


def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![899, 448, 90]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![899, 448, 90]] 
 ![![19, 0, 0], ![10, 1, 0], ![17, 0, 1]] where
  M :=![![![899, 448, 90], ![-8462, 2429, 986], ![-48042, 3926, 2877]]]
  hmulB := by decide  
  f := ![![![3117197, -935556, 223118]], ![![428828, -128703, 30694]], ![![7182345, -2155618, 514087]]]
  g := ![![![-269, 448, 90], ![-2606, 2429, 986], ![-7169, 3926, 2877]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2625343831655, -787937424980, 187912880224]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![2625343831655, -787937424980, 187912880224]] 
 ![![19, 0, 0], ![17, 1, 0], ![8, 0, 1]] where
  M :=![![![2625343831655, -787937424980, 187912880224], ![-19391312567156, 5819862795463, -1387961969736], ![70301376983836, -21099364313844, 5031925370483]]]
  hmulB := by decide  
  f := ![![![-7306555, 1844284, 781568]], ![![-10512757, 1964891, 934568]], ![![-14372676, 740148, 740891]]]
  g := ![![![764051421817, -787937424980, 187912880224], ![-5643436017481, 5819862795463, -1387961969736], ![20459745650280, -21099364313844, 5031925370483]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![899, 448, 90]] ![![899, 448, 90]]
  ![![-7306555, 1844284, 781568]] where
 M := ![![![-7306555, 1844284, 781568]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI19N1 : IdealMulLeCertificate' Table 
  ![![-7306555, 1844284, 781568]] ![![2625343831655, -787937424980, 187912880224]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0]] 
 ![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [7, 7, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 4, 3], [16, 18, 20], [0, 1]]
 g := ![![[17, 0, 18], [15, 18, 6], [22, 12, 1], []], ![[2, 6], [3, 7, 5, 8], [0, 1, 14, 6], [17, 9]], ![[21, 14, 15, 15], [1, 15, 21, 19], [13, 3, 4, 21], [0, 9]]]
 h' := ![![[19, 4, 3], [10, 2, 15], [7, 15, 12], [0, 0, 1], [0, 1]], ![[16, 18, 20], [21, 18], [22, 22, 8], [12, 16, 18], [19, 4, 3]], ![[0, 1], [18, 3, 8], [7, 9, 3], [3, 7, 4], [16, 18, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 14], []]
 b := ![[], [0, 19, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [7, 7, 11, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2610063, 91103, 116679]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-113481, 3961, 5073]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀

instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-724337858, 9318091, 29619988]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-724337858, 9318091, 29619988]] 
 ![![29, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![-724337858, 9318091, 29619988], ![-2923060721, -220798062, 48256170], ![-2136910517, -1056011961, -211479971]]]
  hmulB := by decide  
  f := ![![![97653460460665572, -29308471998221107, 6989691330234726]], ![![-21504636318303221, 6454129002635683, -1539226252964578]], ![![90171082182216063, -27062805810668365, 6454129002635683]]]
  g := ![![![-25298481, 9318091, 29619988], ![-93181471, -220798062, 48256170], ![-37272364, -1056011961, -211479971]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-428828, 128703, -30694]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-428828, 128703, -30694]] 
 ![![29, 0, 0], ![10, 1, 0], ![23, 0, 1]] where
  M :=![![![-428828, 128703, -30694], ![3167409, -950626, 226712], ![-11483143, 3446405, -821923]]]
  hmulB := by decide  
  f := ![![![-3438, -799, -92]], ![![-899, -448, -90]], ![![131, -972, -273]]]
  g := ![![![-34824, 128703, -30694], ![257217, -950626, 226712], ![-932516, 3446405, -821923]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![44360171269, -13313699600, 3175145080]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![44360171269, -13313699600, 3175145080]] 
 ![![29, 0, 0], ![17, 1, 0], ![1, 0, 1]] where
  M :=![![![44360171269, -13313699600, 3175145080], ![-327653062520, 98337637629, -23452254120], ![1187875312120, -356513841480, 85023938029]]]
  hmulB := by decide  
  f := ![![![-2404359, 170000, 136680]], ![![-1870187, 96869, 96560]], ![![-856491, -87720, 7789]]]
  g := ![![![9224755841, -13313699600, 3175145080], ![-68135884417, 98337637629, -23452254120], ![247020230319, -356513841480, 85023938029]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-724337858, 9318091, 29619988]] ![![-428828, 128703, -30694]]
  ![![2404359, -170000, -136680]] where
 M := ![![![2404359, -170000, -136680]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![2404359, -170000, -136680]] ![![44360171269, -13313699600, 3175145080]]
  ![![29, 0, 0]] where
 M := ![![![-29, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1, I29N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1640, -97, -88]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![1640, -97, -88]] 
 ![![31, 0, 0], ![11, 1, 0], ![2, 0, 1]] where
  M :=![![![1640, -97, -88], ![8615, 144, -282], ![13211, 1959, 47]]]
  hmulB := by decide  
  f := ![![![559206, -167833, 40026]], ![![65189, -19565, 4666]], ![![519123, -155803, 37157]]]
  g := ![![![93, -97, -88], ![245, 144, -282], ![-272, 1959, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![129148758, -58564899, -20976974]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![129148758, -58564899, -20976974]] 
 ![![31, 0, 0], ![24, 1, 0], ![7, 0, 1]] where
  M :=![![![129148758, -58564899, -20976974], ![2018155527, -227459800, -138106772], ![6657980935, -135547349, -286024699]]]
  hmulB := by decide  
  f := ![![![46339114006052772, -13907634392698475, 3316790842750828]], ![![24834477687749551, -7453505390062792, 1777564589786250]], ![![50491650915055951, -15153924192824108, 3614014833528199]]]
  g := ![![![54243392, -58564899, -20976974], ![272385101, -227459800, -138106772], ![384299684, -135547349, -286024699]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7035635754, -318122415, -350487788]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![7035635754, -318122415, -350487788]] 
 ![![31, 0, 0], ![26, 1, 0], ![19, 0, 1]] where
  M :=![![![7035635754, -318122415, -350487788], ![34380168597, 1077343358, -986732618], ![45864118393, 8961918253, 759220943]]]
  hmulB := by decide  
  f := ![![![9660958700280222948, -2899517704825057019, 691497453859344574]], ![![5800876147431794413, -1741001448695561348, 415206317566199660]], ![![14266421692734572689, -4281742999417263878, 1021140301109405503]]]
  g := ![![![708583436, -318122415, -350487788], ![810231001, 1077343358, -986732618], ![-6502288842, 8961918253, 759220943]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![1640, -97, -88]] ![![129148758, -58564899, -20976974]]
  ![![-569859445279, -62054667048, 4164293036]] where
 M := ![![![-569859445279, -62054667048, 4164293036]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![-569859445279, -62054667048, 4164293036]] ![![7035635754, -318122415, -350487788]]
  ![![31, 0, 0]] where
 M := ![![![-5951781774474229785874, 151750933335820747709, 264121759007855377464]]]
 hmul := by decide  
 g := ![![![![-191992960466910638254, 4895191397929701539, 8520056742188883144]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1, I31N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)


lemma PB125I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB125I0 : PrimesBelowBoundCertificateInterval O 1 31 125 where
  m := 11
  g := ![3, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB125I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N1]
    · exact ![I3N0]
    · exact ![I5N0]
    · exact ![I7N0, I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N1]
    · exact ![I17N0]
    · exact ![I19N0, I19N0, I19N1]
    · exact ![I23N0]
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0, I31N1, I31N2]
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
    · exact ![2, 2, 2]
    · exact ![27]
    · exact ![125]
    · exact ![7, 7, 7]
    · exact ![1331]
    · exact ![169, 13]
    · exact ![4913]
    · exact ![19, 19, 19]
    · exact ![12167]
    · exact ![29, 29, 29]
    · exact ![31, 31, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N0
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N0
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
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
      exact NI29N2
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
  β := ![I2N0, I2N1, I3N0, I7N0, I7N1, I13N1, I19N0, I19N1, I29N0, I29N1, I29N2, I31N0, I31N1, I31N2]
  Il := ![[I2N0, I2N0, I2N1], [I3N0], [], [I7N0, I7N0, I7N1], [], [I13N1], [], [I19N0, I19N0, I19N1], [], [I29N0, I29N1, I29N2], [I31N0, I31N1, I31N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
