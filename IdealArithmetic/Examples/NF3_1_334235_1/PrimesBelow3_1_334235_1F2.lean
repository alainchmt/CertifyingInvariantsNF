
import IdealArithmetic.Examples.NF3_1_334235_1.RI3_1_334235_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![331, -124, 13]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![331, -124, 13]] 
 ![![83, 0, 0], ![0, 83, 0], ![51, 16, 1]] where
  M :=![![![331, -124, 13], ![-2756, 1046, -111], ![23532, -8861, 935]]]
  hmulB := by decide  
  f := ![![![-67, 9, 2]], ![![-424, 43, 11]], ![![-151, 16, 4]]]
  g := ![![![-4, -4, 13], ![35, 34, -111], ![-291, -287, 935]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [10, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 82], [0, 1]]
 g := ![![[47, 25], [14, 41], [25], [65], [61, 37], [1]], ![[0, 58], [0, 42], [25], [65], [18, 46], [1]]]
 h' := ![![[28, 82], [26, 5], [43, 37], [25, 5], [54, 27], [73, 28], [0, 1]], ![[0, 1], [0, 78], [0, 46], [82, 78], [63, 56], [27, 55], [28, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [46, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [10, 55, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-626, -102, 4]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10, -2, 4]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-67, 9, 2]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-67, 9, 2]] 
 ![![83, 0, 0], ![66, 1, 0], ![43, 0, 1]] where
  M :=![![![-67, 9, 2], ![-424, 43, 11], ![-2332, 181, 54]]]
  hmulB := by decide  
  f := ![![![331, -124, 13]], ![![230, -86, 9]], ![![455, -171, 18]]]
  g := ![![![-9, 9, 2], ![-45, 43, 11], ![-200, 181, 54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![331, -124, 13]] ![![-67, 9, 2]]
  ![![83, 0, 0]] where
 M := ![![![83, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1292260991, 49771214, -12167673]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![1292260991, 49771214, -12167673]] 
 ![![89, 0, 0], ![14, 1, 0], ![71, 0, 1]] where
  M :=![![![1292260991, 49771214, -12167673], ![2579546676, 623038976, 37603541], ![-7971950692, 4647741431, 660642517]]]
  hmulB := by decide  
  f := ![![![-236834501835735421, 89433178012065701, -9452508412491622]], ![![-14738778002832270, 5565640760069047, -588252226688861]], ![![-379451141409515951, 143287912924510820, -15144605530450626]]]
  g := ![![![16397402, 49771214, -12167673], ![-99020791, 623038976, 37603541], ![-1347707297, 4647741431, 660642517]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-50178715743, 6264297404, 1441225355]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-50178715743, 6264297404, 1441225355]] 
 ![![89, 0, 0], ![19, 1, 0], ![84, 0, 1]] where
  M :=![![![-50178715743, 6264297404, 1441225355], ![-305539775260, 29088678782, 7705522759], ![-1633570824908, 118263976485, 36794201541]]]
  hmulB := by decide  
  f := ![![![-159008947291310080947, 60044779702233322389, -6346344811597700026]], ![![-18828594364900889129, 7110032611384826326, -751484455390119979]], ![![-277986738980728075736, 104973039483497423777, -11094971249581514182]]]
  g := ![![![-3261385351, 6264297404, 1441225355], ![-16915602066, 29088678782, 7705522759], ![-78329205703, 118263976485, 36794201541]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2024493, 65486, -20538]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![2024493, 65486, -20538]] 
 ![![89, 0, 0], ![55, 1, 0], ![1, 0, 1]] where
  M :=![![![2024493, 65486, -20538], ![4354056, 894903, 44948], ![-9528976, 6826196, 939851]]]
  hmulB := by decide  
  f := ![![![534251621645, -201743496034, 21322982542]], ![![279363672939, -105492995735, 11149927262]], ![![435768544741, -164554427382, 17392338545]]]
  g := ![![![-17491, 65486, -20538], ![-504613, 894903, 44948], ![-4336063, 6826196, 939851]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![1292260991, 49771214, -12167673]] ![![-50178715743, 6264297404, 1441225355]]
  ![![-60174326853313047869, 8103888634298779307, 1798252715079702138]] where
 M := ![![![-60174326853313047869, 8103888634298779307, 1798252715079702138]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![-60174326853313047869, 8103888634298779307, 1798252715079702138]] ![![2024493, 65486, -20538]]
  ![![89, 0, 0]] where
 M := ![![![-103673225526673206145286913, 15586843772850024661029935, 3290203523768178043525996]]]
 hmul := by decide  
 g := ![![![![-1164867702546889956688617, 175133076099438479337415, 36968578918743573522764]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1, I89N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
    exact isPrimeI89N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [65, 1, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 70, 57], [89, 26, 40], [0, 1]]
 g := ![![[59, 10, 79], [59, 8], [91, 50], [88, 54], [42, 11], [1]], ![[82, 55, 46, 59], [20, 85], [20, 75], [66, 72], [64, 54], [77, 93, 53, 20]], ![[65, 43, 57, 46], [16, 95], [10, 44], [78, 85], [80, 8], [52, 46, 94, 77]]]
 h' := ![![[45, 70, 57], [10, 20, 46], [81, 51, 69], [51, 77, 27], [40, 52, 32], [32, 96, 37], [0, 1]], ![[89, 26, 40], [49, 89, 8], [66, 3, 45], [69, 13, 47], [73, 12, 13], [81, 88, 32], [45, 70, 57]], ![[0, 1], [58, 85, 43], [82, 43, 80], [21, 7, 23], [85, 33, 52], [85, 10, 28], [89, 26, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 87], []]
 b := ![[], [68, 71, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [65, 1, 60, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1249651, -749422, 110095]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![12883, -7726, 1135]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def PBC97 : ContainsPrimesAboveP 97 ![I97N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![97, 0, 0]]) timesTableT_eq_Table B_one_repr 97 (by decide) 𝕀

instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1142951443, 52706774, 22193518]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-1142951443, 52706774, 22193518]] 
 ![![101, 0, 0], ![0, 101, 0], ![40, 24, 1]] where
  M :=![![![-1142951443, 52706774, 22193518], ![-4705025816, 77692047, 74900292], ![-15878861904, -585509756, 152592339]]]
  hmulB := by decide  
  f := ![![![551584780858185, -208288824106594, 22014781380462]], ![![-4667133652657944, 1762397756783595, -186274042726132]], ![![-499581379916072, 188651358375716, -19939228278725]]]
  g := ![![![-20105863, -4751858, 22193518], ![-76247896, -17028861, 74900292], ![-217649064, -42056692, 152592339]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [81, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 100], [0, 1]]
 g := ![![[8, 5], [36], [81, 95], [87], [45], [59, 1]], ![[0, 96], [36], [30, 6], [87], [45], [17, 100]]]
 h' := ![![[59, 100], [29, 56], [4, 95], [48, 14], [5, 84], [69, 67], [0, 1]], ![[0, 1], [0, 45], [54, 6], [66, 87], [12, 17], [83, 34], [59, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [45, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [81, 42, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1701, -353, 141]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-39, -37, 141]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![551584780858185, -208288824106594, 22014781380462]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![551584780858185, -208288824106594, 22014781380462]] 
 ![![101, 0, 0], ![76, 1, 0], ![82, 0, 1]] where
  M :=![![![551584780858185, -208288824106594, 22014781380462], ![-4667133652657944, 1762397756783595, -186274042726132], ![39490097057939984, -14912206002595204, 1576123714057463]]]
  hmulB := by decide  
  f := ![![![-1142951443, 52706774, 22193518]], ![![-906627084, 40429771, 17441660]], ![![-1085157230, 36994512, 19529315]]]
  g := ![![![144320033066945, -208288824106594, 22014781380462], ![-1221137541234340, 1762397756783595, -186274042726132], ![10332431769331322, -14912206002595204, 1576123714057463]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-1142951443, 52706774, 22193518]] ![![551584780858185, -208288824106594, 22014781380462]]
  ![![101, 0, 0]] where
 M := ![![![101, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0)

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![9, 1, 0]] 
 ![![103, 0, 0], ![9, 1, 0], ![22, 0, 1]] where
  M :=![![![9, 1, 0], ![0, 9, 1], ![-212, 55, 10]]]
  hmulB := by decide  
  f := ![![![35, -10, 1]], ![![1, 0, 0]], ![![26, -9, 1]]]
  g := ![![![0, 1, 0], ![-1, 9, 1], ![-9, 55, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![51, -19, 2]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![51, -19, 2]] 
 ![![103, 0, 0], ![84, 1, 0], ![51, 0, 1]] where
  M :=![![![51, -19, 2], ![-424, 161, -17], ![3604, -1359, 144]]]
  hmulB := by decide  
  f := ![![![81, 18, 1]], ![![64, 16, 1]], ![![1, 17, 2]]]
  g := ![![![15, -19, 2], ![-127, 161, -17], ![1072, -1359, 144]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![9, 1, 0]] ![![9, 1, 0]]
  ![![81, 18, 1]] where
 M := ![![![81, 18, 1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI103N1 : IdealMulLeCertificate' Table 
  ![![81, 18, 1]] ![![51, -19, 2]]
  ![![103, 0, 0]] where
 M := ![![![103, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0 ⊙ MulI103N1)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [10, 13, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 39, 88], [78, 67, 19], [0, 1]]
 g := ![![[30, 80, 3], [47, 57, 64], [0, 81], [73, 67, 9], [17, 64], [1]], ![[6, 104, 49, 21], [58, 63, 39, 103], [103, 34], [95, 99, 89, 72], [85, 61], [37, 16, 60, 96]], ![[28, 65, 72, 90], [81, 74, 73, 57], [44, 48], [10, 52, 50, 12], [93, 41], [13, 100, 34, 11]]]
 h' := ![![[21, 39, 88], [65, 98, 18], [40, 69, 8], [19, 71, 98], [37, 41, 3], [97, 94, 99], [0, 1]], ![[78, 67, 19], [46, 86, 93], [19, 20, 81], [34, 36, 81], [106, 49, 64], [10, 24, 32], [21, 39, 88]], ![[0, 1], [91, 30, 103], [27, 18, 18], [57, 0, 35], [75, 17, 40], [91, 96, 83], [78, 67, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70, 53], []]
 b := ![[], [89, 71, 76], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [10, 13, 8, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-903936, 530292, -72546]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8448, 4956, -678]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def PBC107 : ContainsPrimesAboveP 107 ![I107N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![107, 0, 0]]) timesTableT_eq_Table B_one_repr 107 (by decide) 𝕀

instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11093028449774669, 4188936917348728, -442743535797124]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-11093028449774669, 4188936917348728, -442743535797124]] 
 ![![109, 0, 0], ![0, 109, 0], ![20, 32, 1]] where
  M :=![![![-11093028449774669, 4188936917348728, -442743535797124], ![93861629588990288, -35443922918616489, 3746193381551604], ![-794192996888940048, 299902265574328508, -31697729537064885]]]
  hmulB := by decide  
  f := ![![![-390583137, 52379768, 11646036]], ![![-2468959632, 249948843, 64025804]], ![![-921026068, 92646036, 23813955]]]
  g := ![![![-20533557191121, 168410367549144, -442743535797124], ![173740935394112, -1424973496589613, 3746193381551604], ![-1470077120620572, 12057152392297292, -31697729537064885]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [107, 80, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 108], [0, 1]]
 g := ![![[69, 87], [46], [24, 75], [29, 35], [78], [29, 1]], ![[85, 22], [46], [19, 34], [63, 74], [78], [58, 108]]]
 h' := ![![[29, 108], [107, 14], [48, 68], [58, 82], [32, 97], [58, 80], [0, 1]], ![[0, 1], [77, 95], [58, 41], [38, 27], [11, 12], [89, 29], [29, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [103, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [107, 80, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-529, -127, -21]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1, 5, -21]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-390583137, 52379768, 11646036]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-390583137, 52379768, 11646036]] 
 ![![109, 0, 0], ![76, 1, 0], ![1, 0, 1]] where
  M :=![![![-390583137, 52379768, 11646036], ![-2468959632, 249948843, 64025804], ![-13573470448, 1052459588, 313974647]]]
  hmulB := by decide  
  f := ![![![-11093028449774669, 4188936917348728, -442743535797124]], ![![-6873472776090684, 2595553053209971, -274333168247980]], ![![-7387945186593713, 2789827545795204, -294866725439101]]]
  g := ![![![-40211849, 52379768, 11646036], ![-197514656, 249948843, 64025804], ![-861232787, 1052459588, 313974647]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-11093028449774669, 4188936917348728, -442743535797124]] ![![-390583137, 52379768, 11646036]]
  ![![109, 0, 0]] where
 M := ![![![109, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6037, 2280, -241]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-6037, 2280, -241]] 
 ![![113, 0, 0], ![0, 113, 0], ![71, 74, 1]] where
  M :=![![![-6037, 2280, -241], ![51092, -19292, 2039], ![-432268, 163237, -17253]]]
  hmulB := by decide  
  f := ![![![-41, 29, 4]], ![![-848, 179, 33]], ![![-643, 144, 26]]]
  g := ![![![98, 178, -241], ![-829, -1506, 2039], ![7015, 12743, -17253]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [89, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [88, 112], [0, 1]]
 g := ![![[79, 109], [4], [11], [31], [102, 50], [88, 1]], ![[66, 4], [4], [11], [31], [95, 63], [63, 112]]]
 h' := ![![[88, 112], [107, 30], [24, 111], [41, 24], [75, 101], [78, 84], [0, 1]], ![[0, 1], [35, 83], [74, 2], [6, 89], [36, 12], [12, 29], [88, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [73, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [89, 25, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8153, 2446, 482]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-375, -294, 482]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, -29, -4]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![41, -29, -4]] 
 ![![113, 0, 0], ![38, 1, 0], ![25, 0, 1]] where
  M :=![![![41, -29, -4], ![848, -179, -33], ![6996, -967, -212]]]
  hmulB := by decide  
  f := ![![![6037, -2280, 241]], ![![1578, -596, 63]], ![![5161, -1949, 206]]]
  g := ![![![11, -29, -4], ![75, -179, -33], ![434, -967, -212]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-6037, 2280, -241]] ![![41, -29, -4]]
  ![![113, 0, 0]] where
 M := ![![![-113, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![152763047, -13955467, -3783070]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![152763047, -13955467, -3783070]] 
 ![![127, 0, 0], ![0, 127, 0], ![77, 115, 1]] where
  M :=![![![152763047, -13955467, -3783070], ![802010840, -55305803, -17738537], ![3760569844, -173608695, -73044340]]]
  hmulB := by decide  
  f := ![![![-7560721405715, 2855071107190, -301762547847]], ![![63973660143564, -24157661537300, 2553308559343]], ![![49082629556607, -18534527327783, 1958979646947]]]
  g := ![![![3496531, 3315729, -3783070], ![17069907, 15626976, -17738537], ![73897512, 64775515, -73044340]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [122, 83, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 126], [0, 1]]
 g := ![![[85, 76], [98, 30], [98, 120], [120, 31], [93, 26], [44, 1]], ![[0, 51], [21, 97], [44, 7], [87, 96], [94, 101], [88, 126]]]
 h' := ![![[44, 126], [109, 87], [109, 41], [92, 45], [84, 44], [93, 36], [0, 1]], ![[0, 1], [0, 40], [8, 86], [40, 82], [115, 83], [26, 91], [44, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107]]
 b := ![[], [93, 117]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [122, 83, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1100, -244, -22]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![22, 18, -22]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7560721405715, -2855071107190, 301762547847]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![7560721405715, -2855071107190, 301762547847]] 
 ![![127, 0, 0], ![11, 1, 0], ![6, 0, 1]] where
  M :=![![![7560721405715, -2855071107190, 301762547847], ![-63973660143564, 24157661537300, -2553308559343], ![541301414580716, -204405630907429, 21604352977957]]]
  hmulB := by decide  
  f := ![![![-152763047, 13955467, 3783070]], ![![-19546491, 1644220, 467341]], ![![-36827938, 2026311, 753880]]]
  g := ![![![292566364549, -2855071107190, 301762547847], ![-2475496737778, 24157661537300, -2553308559343], ![20945962493659, -204405630907429, 21604352977957]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![152763047, -13955467, -3783070]] ![![7560721405715, -2855071107190, 301762547847]]
  ![![127, 0, 0]] where
 M := ![![![-127, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [20, 100, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 72, 27], [54, 58, 104], [0, 1]]
 g := ![![[116, 34, 77], [19, 127, 114], [29, 21], [99, 123], [24, 7], [92, 1], []], ![[52, 43, 104, 13], [15, 111, 70, 38], [39, 105], [29, 49], [85, 48], [90, 89], [85, 74]], ![[92, 80, 92, 69], [58, 75, 14, 57], [76, 44], [31, 43], [33, 109], [4, 75], [8, 74]]]
 h' := ![![[38, 72, 27], [13, 98, 83], [52, 26, 30], [97, 24, 105], [80, 25, 56], [125, 81, 111], [0, 0, 1], [0, 1]], ![[54, 58, 104], [43, 85, 124], [41, 121, 84], [67, 119, 57], [56, 86, 124], [70, 100, 110], [6, 77, 58], [38, 72, 27]], ![[0, 1], [87, 79, 55], [34, 115, 17], [84, 119, 100], [7, 20, 82], [76, 81, 41], [5, 54, 72], [54, 58, 104]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 76], []]
 b := ![[], [91, 38, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [20, 100, 39, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-38776, -121699, 30392]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-296, -929, 232]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def PBC131 : ContainsPrimesAboveP 131 ![I131N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![131, 0, 0]]) timesTableT_eq_Table B_one_repr 131 (by decide) 𝕀

instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2258342524374853, 852792762157254, -90134678623585]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-2258342524374853, 852792762157254, -90134678623585]] 
 ![![137, 0, 0], ![0, 137, 0], ![134, 24, 1]] where
  M :=![![![-2258342524374853, 852792762157254, -90134678623585], ![19108551868200020, -7215749848672028, 762658083533669], ![-161683513709137828, 61054746462551815, -6453091765138359]]]
  hmulB := by decide  
  f := ![![![236324359, -12277003, -4751858]], ![![1007393896, -25027831, -17028861]], ![![433978366, -15875765, -7937944]]]
  g := ![![![71676674534201, 22014781380462, -90134678623585], ![-606479060768698, -186274042726132, 762658083533669], ![5131611553426294, 1576123714057463, -6453091765138359]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [12, 99, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 136], [0, 1]]
 g := ![![[111, 38], [61], [101], [58, 135], [50], [74], [1]], ![[48, 99], [61], [101], [119, 2], [50], [74], [1]]]
 h' := ![![[38, 136], [115, 77], [5, 91], [126, 52], [4, 51], [78, 119], [125, 38], [0, 1]], ![[0, 1], [27, 60], [38, 46], [47, 85], [24, 86], [79, 18], [62, 99], [38, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [12, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [12, 99, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7846, -3858, 490]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-422, -114, 490]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![236324359, -12277003, -4751858]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![236324359, -12277003, -4751858]] 
 ![![137, 0, 0], ![112, 1, 0], ![60, 0, 1]] where
  M :=![![![236324359, -12277003, -4751858], ![1007393896, -25027831, -17028861], ![3610118532, 70806541, -42056692]]]
  hmulB := by decide  
  f := ![![![-2258342524374853, 852792762157254, -90134678623585]], ![![-1706757743516668, 644503938050660, -68119897243123]], ![![-2169226753077584, 819140964905015, -86577901332507]]]
  g := ![![![13842775, -12277003, -4751858], ![35271844, -25027831, -17028861], ![-13115420, 70806541, -42056692]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-2258342524374853, 852792762157254, -90134678623585]] ![![236324359, -12277003, -4751858]]
  ![![137, 0, 0]] where
 M := ![![![137, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0)


lemma PB164I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB164I2 : PrimesBelowBoundCertificateInterval O 79 137 164 where
  m := 11
  g := ![2, 3, 1, 2, 3, 1, 2, 2, 2, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB164I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0]
    · exact ![I137N0, I137N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![6889, 83]
    · exact ![89, 89, 89]
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![103, 103, 103]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![16129, 127]
    · exact ![2248091]
    · exact ![18769, 137]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N0, I89N1, I89N2, I101N1, I103N0, I103N1, I109N1, I113N1, I127N1, I137N1]
  Il := ![[I83N1], [I89N0, I89N1, I89N2], [], [I101N1], [I103N0, I103N0, I103N1], [], [I109N1], [I113N1], [I127N1], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
