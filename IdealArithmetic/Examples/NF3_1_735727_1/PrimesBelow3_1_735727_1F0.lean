
import IdealArithmetic.Examples.NF3_1_735727_1.RI3_1_735727_1
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
  c := ![5764, -3564, -3014]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2882, -1782, -1507]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3214, -3399, -131]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3214, -3399, -131]] 
 ![![3, 0, 0], ![0, 3, 0], ![1, 0, 1]] where
  M :=![![![3214, -3399, -131], ![-6681, 10419, -3399], ![-173349, 180264, 10419]]]
  hmulB := by decide  
  f := ![![![-240424299, -3933199, -4306030]], ![![-219607530, -3592649, -3933199]], ![![-147005816, -2404928, -2632893]]]
  g := ![![![1115, -1133, -131], ![-1094, 3473, -3399], ![-61256, 60088, 10419]]]
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
  c := ![-611, 1119, -491]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-40, 373, -491]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-240424299, -3933199, -4306030]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-240424299, -3933199, -4306030]] 
 ![![3, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-240424299, -3933199, -4306030], ![-219607530, -3592649, -3933199], ![-200593149, -3281585, -3592649]]]
  hmulB := by decide  
  f := ![![![3214, -3399, -131]], ![![-2227, 3473, -1133]], ![![-57783, 60088, 3473]]]
  g := ![![![-80141433, -3933199, -4306030], ![-73202510, -3592649, -3933199], ![-66864383, -3281585, -3592649]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3214, -3399, -131]] ![![-240424299, -3933199, -4306030]]
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
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-56, -1, -1]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-56, -1, -1]] 
 ![![5, 0, 0], ![0, 5, 0], ![1, 1, 1]] where
  M :=![![![-56, -1, -1], ![-51, -1, -1], ![-51, 4, -1]]]
  hmulB := by decide  
  f := ![![![-1, 1, 0]], ![![0, -1, 1]], ![![10, -11, 0]]]
  g := ![![![-11, 0, -1], ![-10, 0, -1], ![-10, 1, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [4, 3, 1] where
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
 g := ![![[2, 4], [1]], ![[0, 1], [1]]]
 h' := ![![[2, 4], [1, 2], [0, 1]], ![[0, 1], [0, 3], [2, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [4, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 2
  hpos := by decide
  P := [4, 3, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3806, 36, 71]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![747, -7, 71]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -1, 0]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![1, -1, 0]] 
 ![![5, 0, 0], ![4, 1, 0], ![4, 0, 1]] where
  M :=![![![1, -1, 0], ![0, 1, -1], ![-51, 55, 1]]]
  hmulB := by decide  
  f := ![![![56, 1, 1]], ![![55, 1, 1]], ![![55, 0, 1]]]
  g := ![![![1, -1, 0], ![0, 1, -1], ![-55, 55, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-56, -1, -1]] ![![1, -1, 0]]
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


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [5, 3, 3, 1] where
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
 g := ![![[4, 5, 2], [1]], ![[4, 4, 1], [1]], ![[2, 5, 4], [1]]]
 h' := ![![[1, 2], [2, 4, 4], [0, 1]], ![[3, 4], [3, 3, 2], [1, 2]], ![[0, 1], [1, 0, 1], [3, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2], []]
 b := ![[], [5, 3, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [5, 3, 3, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-147735, 237377, -82803]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-21105, 33911, -11829]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11146725497943320, -182353820991791, -199639281867670]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-11146725497943320, -182353820991791, -199639281867670]] 
 ![![11, 0, 0], ![0, 11, 0], ![3, 6, 1]] where
  M :=![![![-11146725497943320, -182353820991791, -199639281867670], ![-10181603375251170, -166564995221470, -182353820991791], ![-9300044870581341, -152143220702665, -166564995221470]]]
  hmulB := by decide  
  f := ![![![-12012535, 13692020, -592071]], ![![-30195621, 20551370, 13692020]], ![![43734699, -56261131, 9175207]]]
  g := ![![![-958891604758210, 92316533655839, -199639281867670], ![-875867446570527, 84323448248116, -182353820991791], ![-800031807719721, 77022431875105, -166564995221470]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [5, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 10], [0, 1]]
 g := ![![[7, 9], [1, 4], [1]], ![[0, 2], [4, 7], [1]]]
 h' := ![![[9, 10], [6, 3], [6, 9], [0, 1]], ![[0, 1], [0, 8], [10, 2], [9, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [7, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [5, 2, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![107, -61, -56]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![25, 25, -56]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12012535, 13692020, -592071]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-12012535, 13692020, -592071]] 
 ![![11, 0, 0], ![5, 1, 0], ![8, 0, 1]] where
  M :=![![![-12012535, 13692020, -592071], ![-30195621, 20551370, 13692020], ![698293020, -783256721, 20551370]]]
  hmulB := by decide  
  f := ![![![-11146725497943320, -182353820991791, -199639281867670]], ![![-5992293714997070, -98030372743675, -107322748211831]], ![![-8952168077647991, -146452162603363, -160334477287530]]]
  g := ![![![-6885097, 13692020, -592071], ![-22044421, 20551370, 13692020], ![404560515, -783256721, 20551370]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-11146725497943320, -182353820991791, -199639281867670]] ![![-12012535, 13692020, -592071]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3606563578826099191364, 59001242057150709970, 64594015795920111915]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![3606563578826099191364, 59001242057150709970, 64594015795920111915]] 
 ![![13, 0, 0], ![0, 13, 0], ![7, 11, 1]] where
  M :=![![![3606563578826099191364, 59001242057150709970, 64594015795920111915], ![3294294805591925707665, 53892710050493036039, 59001242057150709970], ![3009063344914686208470, 49226492448636659315, 53892710050493036039]]]
  hmulB := by decide  
  f := ![![![1114533767, -239951585, -1073146445]], ![![-54730468695, 60137588242, -239951585]], ![![-46651611547, 47561590619, 3845084284]]]
  g := ![![![242646574481127569843, -50117917822920809315, 64594015795920111915], ![221637393168605441375, -45778534813704982587, 59001242057150709970], ![202447259581633458169, -41814870623598979778, 53892710050493036039]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [11, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 12], [0, 1]]
 g := ![![[2, 4], [12], [4, 1]], ![[5, 9], [12], [8, 12]]]
 h' := ![![[4, 12], [10, 11], [8, 5], [0, 1]], ![[0, 1], [2, 2], [2, 8], [4, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [11, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [11, 9, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1959, -1830, 317]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-20, -409, 317]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1114533767, -239951585, -1073146445]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![1114533767, -239951585, -1073146445]] 
 ![![13, 0, 0], ![2, 1, 0], ![9, 0, 1]] where
  M :=![![![1114533767, -239951585, -1073146445], ![-54730468695, 60137588242, -239951585], ![-12237530835, -41533131520, 60137588242]]]
  hmulB := by decide  
  f := ![![![3606563578826099191364, 59001242057150709970, 64594015795920111915]], ![![808263227941855699261, 13222707243445727383, 14476097972999302600]], ![![2728318119565352225442, 44633666997153311465, 48864527093367234098]]]
  g := ![![![865596534, -239951585, -1073146445], ![-13295852378, 60137588242, -239951585], ![-36185350921, -41533131520, 60137588242]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![3606563578826099191364, 59001242057150709970, 64594015795920111915]] ![![1114533767, -239951585, -1073146445]]
  ![![13, 0, 0]] where
 M := ![![![13, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2227, -3473, 1133]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![2227, -3473, 1133]] 
 ![![17, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![2227, -3473, 1133], ![57783, -60088, -3473], ![-177123, 248798, -60088]]]
  hmulB := by decide  
  f := ![![![4474643198, 73202510, 80141433]], ![![240424299, 3933199, 4306030]], ![![219607530, 3592649, 3933199]]]
  g := ![![![131, -3473, 1133], ![3399, -60088, -3473], ![-10419, 248798, -60088]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![837861932050820, 13706924495559, 15006214555992]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![837861932050820, 13706924495559, 15006214555992]] 
 ![![17, 0, 0], ![8, 1, 0], ![4, 0, 1]] where
  M :=![![![837861932050820, 13706924495559, 15006214555992], ![765316942355592, 12520131471260, 13706924495559], ![699053149273509, 11436095099847, 12520131471260]]]
  hmulB := by decide  
  f := ![![![-7091873, 5998884, 1932561]], ![![2460331, -3846568, 1262316]], ![![16327976, -12198969, -6214852]]]
  g := ![![![39304804580140, 13706924495559, 15006214555992], ![35901658388428, 12520131471260, 13706924495559], ![32793168387629, 11436095099847, 12520131471260]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![184, -185, -18]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![184, -185, -18]] 
 ![![17, 0, 0], ![9, 1, 0], ![4, 0, 1]] where
  M :=![![![184, -185, -18], ![-918, 1174, -185], ![-9435, 9257, 1174]]]
  hmulB := by decide  
  f := ![![![3090821, 50564, 55357]], ![![1802388, 29486, 32281]], ![![878944, 14379, 15742]]]
  g := ![![![113, -185, -18], ![-632, 1174, -185], ![-5732, 9257, 1174]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![2227, -3473, 1133]] ![![837861932050820, 13706924495559, 15006214555992]]
  ![![3090821, 50564, 55357]] where
 M := ![![![3090821, 50564, 55357]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![3090821, 50564, 55357]] ![![184, -185, -18]]
  ![![17, 0, 0]] where
 M := ![![![17, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1, I17N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
    exact isPrimeI17N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16, 23, -6]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-16, 23, -6]] 
 ![![19, 0, 0], ![0, 19, 0], ![9, 12, 1]] where
  M :=![![![-16, 23, -6], ![-306, 314, 23], ![1173, -1571, 314]]]
  hmulB := by decide  
  f := ![![![7091, 116, 127]], ![![6477, 106, 116]], ![![7761, 127, 139]]]
  g := ![![![2, 5, -6], ![-27, 2, 23], ![-87, -281, 314]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [3, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 18], [0, 1]]
 g := ![![[4, 9], [17, 9], [11], [1]], ![[10, 10], [4, 10], [11], [1]]]
 h' := ![![[7, 18], [6, 3], [14, 16], [16, 7], [0, 1]], ![[0, 1], [8, 16], [12, 3], [8, 12], [7, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [12, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [3, 12, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-314, 411, -56]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10, 57, -56]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7091, 116, 127]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![7091, 116, 127]] 
 ![![19, 0, 0], ![7, 1, 0], ![8, 0, 1]] where
  M :=![![![7091, 116, 127], ![6477, 106, 116], ![5916, 97, 106]]]
  hmulB := by decide  
  f := ![![![-16, 23, -6]], ![![-22, 25, -1]], ![![55, -73, 14]]]
  g := ![![![277, 116, 127], ![253, 106, 116], ![231, 97, 106]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-16, 23, -6]] ![![7091, 116, 127]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1004976755, -1281174459, 198086160]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![1004976755, -1281174459, 198086160]] 
 ![![23, 0, 0], ![0, 23, 0], ![21, 9, 1]] where
  M :=![![![1004976755, -1281174459, 198086160], ![10102394160, -9889762045, -1281174459], ![-65339897409, 80566989405, -9889762045]]]
  hmulB := by decide  
  f := ![![![-8740337494388356040, -142986739841544615, -156540564400075647]], ![![-7983568784403857997, -130606452384195455, -142986739841544615]], ![![-11421370877117781486, -186846856576047834, -204558215798247199]]]
  g := ![![![-137166635, -133215213, 198086160], ![1609002513, 71339482, -1281174459], ![6188917632, 7372819470, -9889762045]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [4, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 22], [0, 1]]
 g := ![![[0, 6], [0, 3], [], [1]], ![[0, 17], [0, 20], [], [1]]]
 h' := ![![[0, 22], [0, 11], [0, 16], [19], [0, 1]], ![[0, 1], [0, 12], [0, 7], [19], [0, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [0, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [4, 0, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![208, -16, -219]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![209, 85, -219]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8740337494388356040, -142986739841544615, -156540564400075647]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-8740337494388356040, -142986739841544615, -156540564400075647]] 
 ![![23, 0, 0], ![14, 1, 0], ![11, 0, 1]] where
  M :=![![![-8740337494388356040, -142986739841544615, -156540564400075647], ![-7983568784403857997, -130606452384195455, -142986739841544615], ![-7292323731918775365, -119298093118904172, -130606452384195455]]]
  hmulB := by decide  
  f := ![![![1004976755, -1281174459, 198086160]], ![![1050959510, -1209834977, 64870947]], ![![-2360224048, 2890176972, -335252795]]]
  g := ![![![-218112040356778231, -142986739841544615, -156540564400075647], ![-199227144033396994, -130606452384195455, -142986739841544615], ![-181977367479476824, -119298093118904172, -130606452384195455]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![1004976755, -1281174459, 198086160]] ![![-8740337494388356040, -142986739841544615, -156540564400075647]]
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
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-201206356462285443943, -3291616709813468751, -3603631624260650004]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-201206356462285443943, -3291616709813468751, -3603631624260650004]] 
 ![![29, 0, 0], ![0, 29, 0], ![2, 11, 1]] where
  M :=![![![-201206356462285443943, -3291616709813468751, -3603631624260650004], ![-183785212837293150204, -3006617127949693723, -3291616709813468751], ![-167872452200486906301, -2746293797552368899, -3006617127949693723]]]
  hmulB := by decide  
  f := ![![![-1142925020, 1067156013, 201559479]], ![![10279533429, -12228696365, 1067156013]], ![![5697033598, -6234323975, -2995216]]]
  g := ![![![-6689623903922901515, 1253390729553575217, -3603631624260650004], ![-6110413083367800438, 1144867816551671122, -3291616709813468751], ![-5581352342916810995, 1045741193444629726, -3006617127949693723]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [14, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 28], [0, 1]]
 g := ![![[], [5], [0, 22], [0, 1]], ![[], [5], [0, 7], [0, 28]]]
 h' := ![![[0, 28], [17], [0, 11], [0, 15], [0, 1]], ![[0, 1], [17], [0, 18], [0, 14], [0, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [0, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [14, 0, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2022, 2364, -112]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-62, 124, -112]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1142925020, -1067156013, -201559479]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![1142925020, -1067156013, -201559479]] 
 ![![29, 0, 0], ![18, 1, 0], ![24, 0, 1]] where
  M :=![![![1142925020, -1067156013, -201559479], ![-10279533429, 12228696365, -1067156013], ![-54424956663, 48414047286, 12228696365]]]
  hmulB := by decide  
  f := ![![![201206356462285443943, 3291616709813468751, 3603631624260650004]], ![![131224125143394177282, 2146748893261797629, 2350240894707074787]], ![![172304310596390950377, 2818796373554331687, 3085992279662251511]]]
  g := ![![![868591750, -1067156013, -201559479], ![-7061528403, 12228696365, -1067156013], ![-42047121399, 48414047286, 12228696365]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-201206356462285443943, -3291616709813468751, -3603631624260650004]] ![![1142925020, -1067156013, -201559479]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1573068783753414427, -25734472734012522, -28173863470032105]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-1573068783753414427, -25734472734012522, -28173863470032105]] 
 ![![31, 0, 0], ![0, 31, 0], ![3, 17, 1]] where
  M :=![![![-1573068783753414427, -25734472734012522, -28173863470032105], ![-1436867036971637355, -23506292901648652, -25734472734012522], ![-1312458109434638622, -21471036600948645, -23506292901648652]]]
  hmulB := by decide  
  f := ![![![92113406, -83671851, -18800904]], ![![-958846104, 1126163126, -83671851]], ![![-654558321, 726995590, -11376163]]]
  g := ![![![-48017651398171552, 14620038911501073, -28173863470032105], ![-43860116734503219, 13354185276663362, -25734472734012522], ![-40062555829990086, 12197933636357369, -23506292901648652]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [9, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 30], [0, 1]]
 g := ![![[12, 7], [27, 8], [25, 1], [16, 1]], ![[0, 24], [0, 23], [10, 30], [1, 30]]]
 h' := ![![[16, 30], [5, 21], [23, 16], [11, 30], [0, 1]], ![[0, 1], [0, 10], [0, 15], [26, 1], [16, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [26, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [9, 15, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![271, 120, -13]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10, 11, -13]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![92113406, -83671851, -18800904]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![92113406, -83671851, -18800904]] 
 ![![31, 0, 0], ![14, 1, 0], ![21, 0, 1]] where
  M :=![![![92113406, -83671851, -18800904], ![-958846104, 1126163126, -83671851], ![-4267264401, 3643105701, 1126163126]]]
  hmulB := by decide  
  f := ![![![-1573068783753414427, -25734472734012522, -28173863470032105]], ![![-756768709984498043, -12380287457349160, -13553824558531032]], ![![-1107964598976011019, -18125644000490697, -19843787928139447]]]
  g := ![![![53494784, -83671851, -18800904], ![-482839387, 1126163126, -83671851], ![-2545811931, 3643105701, 1126163126]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-1573068783753414427, -25734472734012522, -28173863470032105]] ![![92113406, -83671851, -18800904]]
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


lemma PB243I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB243I0 : PrimesBelowBoundCertificateInterval O 1 31 243 where
  m := 11
  g := ![1, 2, 2, 1, 2, 2, 3, 2, 2, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB243I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0]
    · exact ![I3N0, I3N1]
    · exact ![I5N0, I5N1]
    · exact ![I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1, I17N2]
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
    · exact ![8]
    · exact ![9, 3]
    · exact ![25, 5]
    · exact ![343]
    · exact ![121, 11]
    · exact ![169, 13]
    · exact ![17, 17, 17]
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
    · dsimp ; intro j
      fin_cases j
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
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
      exact NI17N2
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
  β := ![I2N0, I3N0, I3N1, I5N0, I5N1, I11N0, I11N1, I13N0, I13N1, I17N0, I17N1, I17N2, I19N1, I23N1, I29N1, I31N1]
  Il := ![[I2N0], [I3N0, I3N1], [I5N0, I5N1], [], [I11N0, I11N1], [I13N0, I13N1], [I17N0, I17N1, I17N2], [I19N1], [I23N1], [I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
