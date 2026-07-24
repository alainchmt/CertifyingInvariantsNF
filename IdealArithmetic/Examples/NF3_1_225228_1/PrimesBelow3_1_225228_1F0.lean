
import IdealArithmetic.Examples.NF3_1_225228_1.RI3_1_225228_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1637877, 311419, -308829]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![1637877, 311419, -308829]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![1637877, 311419, -308829], ![-27789430, 1323868, 1250856], ![9811979, -4943854, 2260715]]]
  hmulB := by decide  
  f := ![![![9176937684644, 822775882381, 798389155236]], ![![37548677023237, 3366498382323, 3266716802379]], ![![66787028666546, 5987918664270, 5810439302321]]]
  g := ![![![973353, 311419, -308829], ![-14520143, 1323868, 1250856], ![3775632, -4943854, 2260715]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![1637877, 311419, -308829]] ![![1637877, 311419, -308829]]
  ![![-9001739096632, 2449149153121, -814457944104]] where
 M := ![![![-9001739096632, 2449149153121, -814457944104]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-9001739096632, 2449149153121, -814457944104]] ![![1637877, 311419, -308829]]
  ![![2, 0, 0]] where
 M := ![![![-90795644620521263110, 4465598768100288036, 4002273705445011144]]]
 hmul := by decide  
 g := ![![![![-45397822310260631555, 2232799384050144018, 2001136852722505572]]]]
 hle2 := by decide  

def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N0, I2N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-150220394113003, -13468296458498, -13069101880880]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-150220394113003, -13468296458498, -13069101880880]] 
 ![![3, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![-150220394113003, -13468296458498, -13069101880880], ![-1229293965957956, -110214699315127, -106947982512748], ![-2036298488915496, -182568231754702, -177156987029999]]]
  hmulB := by decide  
  f := ![![![20446223, 583742, -1860744]], ![![-49858247, 7241075, -693260]], ![![-13118299, -9303720, 6584321]]]
  g := ![![![-41227665257875, -13468296458498, -13069101880880], ![-337377094710027, -110214699315127, -106947982512748], ![-558857756710265, -182568231754702, -177156987029999]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25686020055, -2302929206, -2234671364]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-25686020055, -2302929206, -2234671364]] 
 ![![3, 0, 0], ![1, 1, 0], ![2, 0, 1]] where
  M :=![![![-25686020055, -2302929206, -2234671364], ![-210195623900, -18845490279, -18286917964], ![-348184440156, -31217141254, -30291878467]]]
  hmulB := by decide  
  f := ![![![164563, -43254, 13972]], ![![454493, 64615, -72536]], ![![-932650, 55442, 35333]]]
  g := ![![![-6304582707, -2302929206, -2234671364], ![-51592099231, -18845490279, -18286917964], ![-85461180656, -31217141254, -30291878467]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-150220394113003, -13468296458498, -13069101880880]] ![![-150220394113003, -13468296458498, -13069101880880]]
  ![![65735254787149056750878704577, 5893619867500990684074646500, 5718935481773526005987534264]] where
 M := ![![![65735254787149056750878704577, 5893619867500990684074646500, 5718935481773526005987534264]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![65735254787149056750878704577, 5893619867500990684074646500, 5718935481773526005987534264]] ![![-25686020055, -2302929206, -2234671364]]
  ![![3, 0, 0]] where
 M := ![![![-4918534526871650793061437981502401146919, -440980610791324767993103652542383476418, -427910133080574822040639126995523652316]]]
 hmul := by decide  
 g := ![![![![-1639511508957216931020479327167467048973, -146993536930441589331034550847461158806, -142636711026858274013546375665174550772]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3806613538, -341289210, -331173543]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-3806613538, -341289210, -331173543]] 
 ![![5, 0, 0], ![0, 5, 0], ![1, 0, 1]] where
  M :=![![![-3806613538, -341289210, -331173543], ![-31150544376, -2792861575, -2710082346], ![-51600193443, -4626313935, -4489191958]]]
  hmulB := by decide  
  f := ![![![15532, -9705, 4713]], ![![414186, 30229, -48804]], ![![-117967, 14139, 167]]]
  g := ![![![-695087999, -68257842, -331173543], ![-5688092406, -558572315, -2710082346], ![-9422200297, -925262787, -4489191958]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [3, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 4], [0, 1]]
 g := ![![[4, 4], [1]], ![[1, 1], [1]]]
 h' := ![![[3, 4], [2, 3], [0, 1]], ![[0, 1], [1, 2], [3, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [4, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 2
  hpos := by decide
  P := [3, 2, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1002719, 257675, 15744]
  a := ![-65, 2, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![197395, 51535, 15744]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15532, 9705, -4713]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![-15532, 9705, -4713]] 
 ![![5, 0, 0], ![3, 1, 0], ![4, 0, 1]] where
  M :=![![![-15532, 9705, -4713], ![-414186, -30229, 48804], ![605367, -80400, 3878]]]
  hmulB := by decide  
  f := ![![![3806613538, 341289210, 331173543]], ![![8514076998, 763345841, 740720595]], ![![13365329519, 1198294155, 1162777226]]]
  g := ![![![-5159, 9705, -4713], ![-103743, -30229, 48804], ![166211, -80400, 3878]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-3806613538, -341289210, -331173543]] ![![-15532, 9705, -4713]]
  ![![5, 0, 0]] where
 M := ![![![-5, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [6, 5, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 4], [2, 2], [0, 1]]
 g := ![![[6, 5, 1], [1]], ![[2, 5, 2], [1]], ![[6, 4, 4], [1]]]
 h' := ![![[6, 4], [1, 2, 1], [0, 1]], ![[2, 2], [0, 0, 2], [6, 4]], ![[0, 1], [2, 5, 4], [2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3], []]
 b := ![[], [3, 3, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [6, 5, 6, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-481768, -7567, 22428]
  a := ![-2, 4, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-68824, -1081, 3204]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9545823, 855849, 830482]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![9545823, 855849, 830482]] 
 ![![11, 0, 0], ![0, 11, 0], ![3, 4, 1]] where
  M :=![![![9545823, 855849, 830482], ![78116042, 7003643, 6796058], ![129397510, 11601381, 11257521]]]
  hmulB := by decide  
  f := ![![![-645, 483, -244]], ![![-21482, -1367, 2410]], ![![-5301, -742, 839]]]
  g := ![![![641307, -224189, 830482], ![5247988, -1834599, 6796058], ![8693177, -3038973, 11257521]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [4, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 10], [0, 1]]
 g := ![![[8, 3], [4, 1], [1]], ![[0, 8], [5, 10], [1]]]
 h' := ![![[1, 10], [6, 5], [7, 1], [0, 1]], ![[0, 1], [0, 6], [8, 10], [1, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [8, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [4, 10, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![544, 135, -24]
  a := ![-1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![56, 21, -24]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![645, -483, 244]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![645, -483, 244]] 
 ![![11, 0, 0], ![7, 1, 0], ![0, 0, 1]] where
  M :=![![![645, -483, 244], ![21482, 1367, -2410], ![-29552, 4143, -321]]]
  hmulB := by decide  
  f := ![![![-9545823, -855849, -830482]], ![![-13176073, -1181326, -1146312]], ![![-11763410, -1054671, -1023411]]]
  g := ![![![366, -483, 244], ![1083, 1367, -2410], ![-5323, 4143, -321]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![9545823, 855849, 830482]] ![![645, -483, 244]]
  ![![11, 0, 0]] where
 M := ![![![-11, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0]] 
 ![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [12, 6, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 7, 1], [8, 5, 12], [0, 1]]
 g := ![![[6, 8, 12], [2, 1], [1]], ![[8, 1, 2, 3], [4, 1], [8, 12, 9, 1]], ![[5, 9, 11, 12], [], [3, 8, 1, 12]]]
 h' := ![![[6, 7, 1], [3, 3, 8], [1, 7, 1], [0, 1]], ![[8, 5, 12], [0, 7, 4], [3, 5, 12], [6, 7, 1]], ![[0, 1], [12, 3, 1], [8, 1], [8, 5, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 4], []]
 b := ![[], [3, 11, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [12, 6, 12, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4630730, 480129, 164957]
  a := ![2, 18, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![356210, 36933, 12689]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def PBC13 : ContainsPrimesAboveP 13 ![I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![13, 0, 0]]) timesTableT_eq_Table B_one_repr 13 (by decide) 𝕀

instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, -2, 2]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-11, -2, 2]] 
 ![![17, 0, 0], ![0, 17, 0], ![3, 16, 1]] where
  M :=![![![-11, -2, 2], ![180, -9, -8], ![-62, 32, -15]]]
  hmulB := by decide  
  f := ![![![-23, -2, -2]], ![![-188, -17, -16]], ![![-199, -18, -17]]]
  g := ![![![-1, -2, 2], ![12, 7, -8], ![-1, 16, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [14, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 16], [0, 1]]
 g := ![![[13, 1], [4], [8], [1]], ![[1, 16], [4], [8], [1]]]
 h' := ![![[5, 16], [13, 16], [16, 2], [3, 5], [0, 1]], ![[0, 1], [8, 1], [9, 15], [11, 12], [5, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [13, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [14, 12, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2129, 415, -24]
  a := ![-2, 4, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-121, 47, -24]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 2, 2]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![23, 2, 2]] 
 ![![17, 0, 0], ![4, 1, 0], ![16, 0, 1]] where
  M :=![![![23, 2, 2], ![188, 17, 16], ![306, 28, 27]]]
  hmulB := by decide  
  f := ![![![11, 2, -2]], ![![-8, 1, 0]], ![![14, 0, -1]]]
  g := ![![![-1, 2, 2], ![-8, 17, 16], ![-14, 28, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-11, -2, 2]] ![![23, 2, 2]]
  ![![17, 0, 0]] where
 M := ![![![-17, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0]] 
 ![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [13, 9, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 10, 1], [13, 8, 18], [0, 1]]
 g := ![![[1, 8, 6], [10, 6, 5], [0, 1], []], ![[17, 11, 2, 1], [16, 17, 7, 5], [10, 7], [1, 1]], ![[0, 16, 6, 3], [5, 0, 6, 18], [16, 5], [3, 1]]]
 h' := ![![[6, 10, 1], [3, 3, 14], [0, 6, 10], [0, 0, 1], [0, 1]], ![[13, 8, 18], [1, 15, 1], [0, 14, 10], [4, 3, 8], [6, 10, 1]], ![[0, 1], [0, 1, 4], [10, 18, 18], [16, 16, 10], [13, 8, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 1], []]
 b := ![[], [0, 6, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [13, 9, 0, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![304171, -1653, 9918]
  a := ![2, -1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![16009, -87, 522]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6318505333, 3295753036, -1523490282]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-6318505333, 3295753036, -1523490282]] 
 ![![23, 0, 0], ![0, 23, 0], ![21, 3, 1]] where
  M :=![![![-6318505333, 3295753036, -1523490282], ![-133569599872, -11386521123, 16727537652], ![210276372110, -26148107266, 273000739]]]
  hmulB := by decide  
  f := ![![![18881953049536159545, 1692897578176308496, 1642720814117612382]], ![![154516110055172956136, 13853437079065930171, 13442827097293075740]], ![![48522690915616215469, 4350394565760354181, 4221450721488602773]]]
  g := ![![![1116295243, 342009734, -1523490282], ![-21080343068, -2676918873, 16727537652], ![8893189417, -1172483021, 273000739]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [12, 6, 1] where
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
 g := ![![[12, 2], [9, 13], [20, 13], [1]], ![[0, 21], [0, 10], [11, 10], [1]]]
 h' := ![![[17, 22], [7, 5], [13, 6], [11, 17], [0, 1]], ![[0, 1], [0, 18], [0, 17], [1, 6], [17, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [12, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [12, 6, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6107, 1500, 40]
  a := ![-5, 0, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![229, 60, 40]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18881953049536159545, -1692897578176308496, -1642720814117612382]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-18881953049536159545, -1692897578176308496, -1642720814117612382]] 
 ![![23, 0, 0], ![3, 1, 0], ![19, 0, 1]] where
  M :=![![![-18881953049536159545, -1692897578176308496, -1642720814117612382], ![-154516110055172956136, -13853437079065930171, -13442827097293075740], ![-255952546853394736934, -22947914633587877234, -22267748205888776537]]]
  hmulB := by decide  
  f := ![![![6318505333, -3295753036, 1523490282]], ![![6631526777, 65185305, -528568122]], ![![-3922816121, -1585704366, 1246665853]]]
  g := ![![![756888484922930487, -1692897578176308496, -1642720814117612382], ![6193822436112751019, -13853437079065930171, -13442827097293075740], ![10259930998228506477, -22947914633587877234, -22267748205888776537]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-6318505333, 3295753036, -1523490282]] ![![-18881953049536159545, -1692897578176308496, -1642720814117612382]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, -37, 14]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![113, -37, 14]] 
 ![![29, 0, 0], ![0, 29, 0], ![6, 16, 1]] where
  M :=![![![113, -37, 14], ![1214, 173, -194], ![-2550, 247, 39]]]
  hmulB := by decide  
  f := ![![![-1885, -169, -164]], ![![-15426, -1383, -1342]], ![![-9782, -877, -851]]]
  g := ![![![1, -9, 14], ![82, 113, -194], ![-96, -13, 39]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [9, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 28], [0, 1]]
 g := ![![[2, 13], [25], [11, 16], [11, 1]], ![[0, 16], [25], [13, 13], [22, 28]]]
 h' := ![![[11, 28], [6, 10], [17, 5], [17, 25], [0, 1]], ![[0, 1], [0, 19], [14, 24], [2, 4], [11, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [9, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [9, 18, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15595, 1140, 644]
  a := ![4, -12, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-671, -316, 644]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1885, -169, -164]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-1885, -169, -164]] 
 ![![29, 0, 0], ![18, 1, 0], ![20, 0, 1]] where
  M :=![![![-1885, -169, -164], ![-15426, -1383, -1342], ![-25552, -2291, -2223]]]
  hmulB := by decide  
  f := ![![![113, -37, 14]], ![![112, -17, 2]], ![![-10, -17, 11]]]
  g := ![![![153, -169, -164], ![1252, -1383, -1342], ![2074, -2291, -2223]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![113, -37, 14]] ![![-1885, -169, -164]]
  ![![29, 0, 0]] where
 M := ![![![29, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0]] 
 ![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [19, 21, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 1, 3], [16, 29, 28], [0, 1]]
 g := ![![[23, 0, 7], [24, 29, 25], [5, 8, 14], [1]], ![[30, 7, 4, 12], [25, 22, 30, 29], [2, 3, 10, 17], [13, 28, 6, 27]], ![[19, 5, 22, 2], [27, 0, 19, 8], [17, 19, 23, 1], [5, 7, 29, 4]]]
 h' := ![![[28, 1, 3], [9, 3, 21], [29, 11, 26], [12, 10, 13], [0, 1]], ![[16, 29, 28], [30, 13, 29], [11, 16, 12], [5, 28, 4], [28, 1, 3]], ![[0, 1], [28, 15, 12], [20, 4, 24], [2, 24, 14], [16, 29, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 6], []]
 b := ![[], [25, 4, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [19, 21, 18, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![36009197, 270909, 1784360]
  a := ![14, -2, 29]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1161587, 8739, 57560]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def PBC31 : ContainsPrimesAboveP 31 ![I31N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![31, 0, 0]]) timesTableT_eq_Table B_one_repr 31 (by decide) 𝕀



lemma PB135I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB135I0 : PrimesBelowBoundCertificateInterval O 1 31 135 where
  m := 11
  g := ![3, 3, 2, 1, 2, 1, 2, 1, 2, 2, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB135I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N0]
    · exact ![I3N0, I3N0, I3N1]
    · exact ![I5N0, I5N1]
    · exact ![I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0]
    · exact ![I17N0, I17N1]
    · exact ![I19N0]
    · exact ![I23N0, I23N1]
    · exact ![I29N0, I29N1]
    · exact ![I31N0]
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
    · exact ![3, 3, 3]
    · exact ![25, 5]
    · exact ![343]
    · exact ![121, 11]
    · exact ![2197]
    · exact ![289, 17]
    · exact ![6859]
    · exact ![529, 23]
    · exact ![841, 29]
    · exact ![29791]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N0
      exact NI2N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
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
  β := ![I2N0, I3N0, I3N1, I5N0, I5N1, I11N0, I11N1, I17N1, I23N1, I29N1]
  Il := ![[I2N0, I2N0, I2N0], [I3N0, I3N0, I3N1], [I5N0, I5N1], [], [I11N0, I11N1], [], [I17N1], [], [I23N1], [I29N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
