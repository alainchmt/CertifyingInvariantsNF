
import IdealArithmetic.Examples.NF3_1_504175_1.RI3_1_504175_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0]] 
 ![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P0 : CertificateIrreducibleZModOfList' 2 3 2 1 [1, 1, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 1], [0, 1, 1], [0, 1]]
 g := ![![[]], ![[0, 1]], ![[0, 1]]]
 h' := ![![[0, 0, 1], [0, 1]], ![[0, 1, 1], [0, 0, 1]], ![[0, 1], [0, 1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1], []]
 b := ![[], [1, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where
  n := 3
  hpos := by decide
  P := [1, 1, 0, 1]
  hirr := P2P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-516704, -187416, -17666]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-258352, -93708, -8833]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 8 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def PBC2 : ContainsPrimesAboveP 2 ![I2N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![2, 0, 0]]) timesTableT_eq_Table B_one_repr 2 (by decide) 𝕀

instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4721, -387, 58]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-4721, -387, 58]] 
 ![![3, 0, 0], ![0, 3, 0], ![1, 0, 1]] where
  M :=![![![-4721, -387, 58], ![32190, 2529, -387], ![-214785, -16185, 2529]]]
  hmulB := by decide  
  f := ![![![44082, 13331, 1029]], ![![571095, 172707, 13331]], ![![2480929, 750267, 57912]]]
  g := ![![![-1593, -129, 58], ![10859, 843, -387], ![-72438, -5395, 2529]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 2], [0, 1]]
 g := ![![[1, 1]], ![[2, 2]]]
 h' := ![![[1, 2], [0, 1]], ![[0, 1], [1, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [2, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 2
  hpos := by decide
  P := [2, 2, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6659, 3495, 1129]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2596, 1165, 1129]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![44082, 13331, 1029]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![44082, 13331, 1029]] 
 ![![3, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![44082, 13331, 1029], ![571095, 172707, 13331], ![7398705, 2237470, 172707]]]
  hmulB := by decide  
  f := ![![![-4721, -387, 58]], ![![10730, 843, -129]], ![![-71595, -5395, 843]]]
  g := ![![![14694, 13331, 1029], ![190365, 172707, 13331], ![2466235, 2237470, 172707]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-4721, -387, 58]] ![![44082, 13331, 1029]]
  ![![3, 0, 0]] where
 M := ![![![3, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12321710, 909441, -143612]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![12321710, 909441, -143612]] 
 ![![5, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![12321710, 909441, -143612], ![-79704660, -5629790, 909441], ![504739755, 33975465, -5629790]]]
  hmulB := by decide  
  f := ![![![795854579035, 240677367810, 18577531001]], ![![2062105941111, 623609190832, 48135473562]], ![![26715187826910, 8079040136361, 623609190832]]]
  g := ![![![2464342, 909441, -143612], ![-15940932, -5629790, 909441], ![100947951, 33975465, -5629790]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![12321710, 909441, -143612]] ![![12321710, 909441, -143612]]
  ![![6851165933980, 1206621937140, -133957082559]] where
 M := ![![![6851165933980, 1206621937140, -133957082559]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![6851165933980, 1206621937140, -133957082559]] ![![12321710, 909441, -143612]]
  ![![5, 0, 0]] where
 M := ![![![-79368776479248799645, -5113551087312110355, 867592062843635590]]]
 hmul := by decide  
 g := ![![![![-15873755295849759929, -1022710217462422071, 173518412568727118]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 13, 1]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![43, 13, 1]] 
 ![![7, 0, 0], ![4, 1, 0], ![5, 0, 1]] where
  M :=![![![43, 13, 1], ![555, 168, 13], ![7215, 2180, 168]]]
  hmulB := by decide  
  f := ![![![-116, -4, 1]], ![![13, -1, 0]], ![![-400, 5, 2]]]
  g := ![![![-2, 13, 1], ![-26, 168, 13], ![-335, 2180, 168]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1288, -69, 13]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-1288, -69, 13]] 
 ![![7, 0, 0], ![6, 1, 0], ![6, 0, 1]] where
  M :=![![![-1288, -69, 13], ![7215, 337, -69], ![-38295, -1410, 337]]]
  hmulB := by decide  
  f := ![![![-16279, -4923, -380]], ![![-44082, -13331, -1029]], ![![-404277, -122259, -9437]]]
  g := ![![![-136, -69, 13], ![801, 337, -69], ![-4551, -1410, 337]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![43, 13, 1]] ![![43, 13, 1]]
  ![![16279, 4923, 380]] where
 M := ![![![16279, 4923, 380]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![16279, 4923, 380]] ![![-1288, -69, 13]]
  ![![7, 0, 0]] where
 M := ![![![-7, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-65781589, -5763937, 836841]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-65781589, -5763937, 836841]] 
 ![![11, 0, 0], ![0, 11, 0], ![10, 6, 1]] where
  M :=![![![-65781589, -5763937, 836841], ![464446755, 38823536, -5763937], ![-3198985035, -256045370, 38823536]]]
  hmulB := by decide  
  f := ![![![2857960520146, 864286558642, 66713004563]], ![![37025717532465, 11197086090521, 864286558642]], ![![66401177312960, 20080629044751, 1549994135273]]]
  g := ![![![-6740909, -980453, 836841], ![47462375, 6673378, -5763937], ![-326110945, -44453326, 38823536]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [9, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 10], [0, 1]]
 g := ![![[2, 5], [3, 5], [1]], ![[0, 6], [1, 6], [1]]]
 h' := ![![[4, 10], [6, 4], [2, 4], [0, 1]], ![[0, 1], [0, 7], [7, 7], [4, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [2, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [9, 7, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2547, 184, 247]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7, -118, 247]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2857960520146, -864286558642, -66713004563]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-2857960520146, -864286558642, -66713004563]] 
 ![![11, 0, 0], ![5, 1, 0], ![8, 0, 1]] where
  M :=![![![-2857960520146, -864286558642, -66713004563], ![-37025717532465, -11197086090521, -864286558642], ![-479679040046310, -145061537362715, -11197086090521]]]
  hmulB := by decide  
  f := ![![![65781589, 5763937, -836841]], ![![-12321710, -909441, 143612]], ![![338657977, 27468806, -4138024]]]
  g := ![![![181561482688, -864286558642, -66713004563], ![2352182308116, -11197086090521, -864286558642], ![30473212317403, -145061537362715, -11197086090521]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-65781589, -5763937, 836841]] ![![-2857960520146, -864286558642, -66713004563]]
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


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [1, 10, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 11, 1], [1, 1, 12], [0, 1]]
 g := ![![[7, 7, 9], [8, 10], [1]], ![[1, 0, 3, 4], [4, 9], [7, 1, 1, 1]], ![[4, 5, 2, 12], [11, 3], [1, 8, 9, 12]]]
 h' := ![![[6, 11, 1], [6, 8, 3], [12, 3, 7], [0, 1]], ![[1, 1, 12], [10, 1, 11], [1, 12, 10], [6, 11, 1]], ![[0, 1], [2, 4, 12], [0, 11, 9], [1, 1, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 10], []]
 b := ![[], [7, 3, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [1, 10, 6, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6472947, -3291015, -397956]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-497919, -253155, -30612]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![44, 13, 1]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![44, 13, 1]] 
 ![![17, 0, 0], ![0, 17, 0], ![10, 13, 1]] where
  M :=![![![44, 13, 1], ![555, 169, 13], ![7215, 2180, 169]]]
  hmulB := by decide  
  f := ![![![13, -1, 0]], ![![0, 13, -1]], ![![-25, 2, 0]]]
  g := ![![![2, 0, 1], ![25, 0, 13], ![325, -1, 169]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [14, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 16], [0, 1]]
 g := ![![[], [], [], [1]], ![[], [], [], [1]]]
 h' := ![![[0, 16], [13], [9], [3], [0, 1]], ![[0, 1], [13], [9], [3], [0, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [0, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [14, 0, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1124, 805, 126]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8, -49, 126]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, -1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![13, -1, 0]] 
 ![![17, 0, 0], ![4, 1, 0], ![1, 0, 1]] where
  M :=![![![13, -1, 0], ![0, 13, -1], ![-555, -125, 13]]]
  hmulB := by decide  
  f := ![![![44, 13, 1]], ![![43, 13, 1]], ![![427, 129, 10]]]
  g := ![![![1, -1, 0], ![-3, 13, -1], ![-4, -125, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![44, 13, 1]] ![![13, -1, 0]]
  ![![17, 0, 0]] where
 M := ![![![17, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [11, 16, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 16, 18], [3, 2, 1], [0, 1]]
 g := ![![[17, 4, 7], [2, 1, 1], [6, 1], []], ![[1, 14, 8, 10], [10, 17, 15, 13], [14, 4], [12, 1]], ![[3, 11, 0, 6], [4, 3, 13, 16], [1, 9], [10, 1]]]
 h' := ![![[3, 16, 18], [16, 0, 11], [10, 7, 1], [0, 0, 1], [0, 1]], ![[3, 2, 1], [12, 1, 3], [3, 5, 14], [10, 7, 2], [3, 16, 18]], ![[0, 1], [7, 18, 5], [6, 7, 4], [13, 12, 16], [3, 2, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 16], []]
 b := ![[], [0, 18, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [11, 16, 13, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8406626, 2573550, 190456]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![442454, 135450, 10024]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![519962, -7708, -2503]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![519962, -7708, -2503]] 
 ![![23, 0, 0], ![3, 1, 0], ![14, 0, 1]] where
  M :=![![![519962, -7708, -2503], ![-1389165, 207087, -7708], ![-4277940, -2352665, 207087]]]
  hmulB := by decide  
  f := ![![![24750683749, 7484947091, 577752025]], ![![17169757614, 5192370789, 400791442]], ![![195680661217, 59176522588, 4567748488]]]
  g := ![![![25136, -7708, -2503], ![-82718, 207087, -7708], ![-5181, -2352665, 207087]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![7, 1, 0]] 
 ![![23, 0, 0], ![7, 1, 0], ![20, 0, 1]] where
  M :=![![![7, 1, 0], ![0, 7, 1], ![555, 125, 7]]]
  hmulB := by decide  
  f := ![![![-76, -7, 1]], ![![1, 0, 0]], ![![-235, -20, 3]]]
  g := ![![![0, 1, 0], ![-3, 7, 1], ![-20, 125, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1240306672, 375085792, 28952319]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![1240306672, 375085792, 28952319]] 
 ![![23, 0, 0], ![13, 1, 0], ![15, 0, 1]] where
  M :=![![![1240306672, 375085792, 28952319], ![16068537045, 4859346547, 375085792], ![208172614560, 62954261045, 4859346547]]]
  hmulB := by decide  
  f := ![![![2250569, 153131, -25229]], ![![663274, 47289, -7602]], ![![5162880, 323315, -55717]]]
  g := ![![![-176960583, 375085792, 28952319], ![-2292576302, 4859346547, 375085792], ![-29700999010, 62954261045, 4859346547]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![519962, -7708, -2503]] ![![7, 1, 0]]
  ![![2250569, 153131, -25229]] where
 M := ![![![2250569, 153131, -25229]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![2250569, 153131, -25229]] ![![1240306672, 375085792, 28952319]]
  ![![23, 0, 0]] where
 M := ![![![23, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1, I23N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
    exact isPrimeI23N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1)
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1664244829681, -144053887770, 21034991598]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-1664244829681, -144053887770, 21034991598]] 
 ![![29, 0, 0], ![0, 29, 0], ![19, 17, 1]] where
  M :=![![![-1664244829681, -144053887770, 21034991598], ![11674420336890, 965129120069, -144053887770], ![-79949907712350, -6332315634360, 965129120069]]]
  hmulB := by decide  
  f := ![![![-664811472029324923709, -201048130390756570650, -15518608621214048022]], ![![-8612827784773796652210, -2604637549681080926459, -201048130390756570650]], ![![-9332110437123503908579, -2822158513986935123297, -217838252763000328963]]]
  g := ![![![-71169298967, -17298232584, 21034991598], ![496946351880, 117725696971, -144053887770], ![-3389219344609, -784121057777, 965129120069]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [6, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 28], [0, 1]]
 g := ![![[12, 5], [9], [3, 24], [15, 1]], ![[0, 24], [9], [15, 5], [1, 28]]]
 h' := ![![[15, 28], [9, 11], [11, 26], [26, 16], [0, 1]], ![[0, 1], [0, 18], [24, 3], [5, 13], [15, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [7, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [6, 14, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3337, -159, 122]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-195, -77, 122]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![821934929, 80507841, -11111426]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![821934929, 80507841, -11111426]] 
 ![![29, 0, 0], ![12, 1, 0], ![1, 0, 1]] where
  M :=![![![821934929, 80507841, -11111426], ![-6166841430, -566993321, 80507841], ![44681851755, 3896638695, -566993321]]]
  hmulB := by decide  
  f := ![![![7771457567101546, 2350195626900891, 181408133695535]], ![![6687551896766913, 2022407648339797, 156106663146459]], ![![45245863120589519, 13682971144501179, 1056168359059964]]]
  g := ![![![-4587853, 80507841, -11111426], ![19192089, -566993321, 80507841], ![-52097216, 3896638695, -566993321]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-1664244829681, -144053887770, 21034991598]] ![![821934929, 80507841, -11111426]]
  ![![29, 0, 0]] where
 M := ![![![460338903579643037941, 29658596306410240059, -5032033964493086422]]]
 hmul := by decide  
 g := ![![![![15873755295849759929, 1022710217462422071, -173518412568727118]]]]
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


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [12, 21, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 10, 16], [22, 20, 15], [0, 1]]
 g := ![![[17, 29, 14], [20], [27, 20, 16], [1]], ![[2, 16, 14, 9], [22, 7, 5, 18], [19, 11, 4, 1], [24, 7, 8, 4]], ![[19, 29, 12, 13], [28, 27, 11, 13], [23, 28, 28, 23], [23, 8, 30, 27]]]
 h' := ![![[13, 10, 16], [8, 24, 13], [17, 19], [19, 10, 4], [0, 1]], ![[22, 20, 15], [26, 20, 24], [16, 4, 25], [18, 18, 23], [13, 10, 16]], ![[0, 1], [27, 18, 25], [1, 8, 6], [18, 3, 4], [22, 20, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 14], []]
 b := ![[], [28, 10, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [12, 21, 27, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3357207, 1374416, 145979]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![108297, 44336, 4709]
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



lemma PB201I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB201I0 : PrimesBelowBoundCertificateInterval O 1 31 201 where
  m := 11
  g := ![1, 2, 3, 3, 2, 1, 2, 1, 3, 2, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB201I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0]
    · exact ![I3N0, I3N1]
    · exact ![I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0]
    · exact ![I17N0, I17N1]
    · exact ![I19N0]
    · exact ![I23N0, I23N1, I23N2]
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
    · exact ![8]
    · exact ![9, 3]
    · exact ![5, 5, 5]
    · exact ![7, 7, 7]
    · exact ![121, 11]
    · exact ![2197]
    · exact ![289, 17]
    · exact ![6859]
    · exact ![23, 23, 23]
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
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N0
      exact NI7N1
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
      exact NI23N2
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
  β := ![I2N0, I3N0, I3N1, I5N0, I7N0, I7N1, I11N0, I11N1, I17N1, I23N0, I23N1, I23N2, I29N1]
  Il := ![[I2N0], [I3N0, I3N1], [I5N0, I5N0, I5N0], [I7N0, I7N0, I7N1], [I11N0, I11N1], [], [I17N1], [], [I23N0, I23N1, I23N2], [I29N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
