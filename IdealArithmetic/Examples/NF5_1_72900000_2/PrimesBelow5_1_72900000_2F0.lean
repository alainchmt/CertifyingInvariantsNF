
import IdealArithmetic.Examples.NF5_1_72900000_2.RI5_1_72900000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 0, 0, 0, -1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![0, 0, 0, 0, -1]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![0, 0, 0, 0, -1], ![0, -1, -1, 1, -6], ![-4, -2, 0, -1, 22], ![4, 14, 13, -16, 74], ![2, 2, 1, -1, -3]]]
  hmulB := by decide  
  f := ![![![-7, 6, -3, 1, -7]], ![![-2, -5, 3, -1, 8]], ![![4, 2, -4, 1, -10]], ![![-4, -2, -1, 0, -2]], ![![-1, 0, 0, 0, 0]]]
  g := ![![![0, 0, 0, 0, -1], ![0, -1, -1, 1, -6], ![-2, -2, 0, -1, 22], ![2, 14, 13, -16, 74], ![1, 2, 1, -1, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-77, -245, -268, 40, -591]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-77, -245, -268, 40, -591]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-77, -245, -268, 40, -591], ![-160, -508, -556, 83, -1226], ![-332, -1054, -1153, 172, -2542], ![-688, -2186, -2392, 357, -5276], ![-50, -159, -174, 26, -384]]]
  hmulB := by decide  
  f := ![![![14, 1, -4, 1, -12]], ![![-2, 3, -2, 1, -7]], ![![-4, -5, 3, -1, 16]], ![![4, 8, 4, -7, 38]], ![![9, 2, -2, 0, -7]]]
  g := ![![![257, -245, -268, 40, -591], ![533, -508, -556, 83, -1226], ![1105, -1054, -1153, 172, -2542], ![2294, -2186, -2392, 357, -5276], ![167, -159, -174, 26, -384]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, 19, 6, -4, -84]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![25, 19, 6, -4, -84]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![25, 19, 6, -4, -84], ![16, -75, -93, 114, -736], ![-456, -264, -13, -41, 2196], ![164, 1576, 1645, -1963, 10798], ![208, 255, 155, -161, 51]]]
  hmulB := by decide  
  f := ![![![-2154, -6864, -7529, 1125, -16606]], ![![-3327, -10562, -11562, 1726, -25496]], ![![-5731, -18221, -19943, 2977, -43978]], ![![-10735, -34103, -37327, 5572, -82312]], ![![-1779, -5662, -6206, 927, -13687]]]
  g := ![![![44, 19, 6, -4, -84], ![403, -75, -93, 114, -736], ![-1167, -264, -13, -41, 2196], ![-5946, 1576, 1645, -1963, 10798], ![-46, 255, 155, -161, 51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![0, 0, 0, 0, -1]] ![![-77, -245, -268, 40, -591]]
  ![![50, 159, 174, -26, 384]] where
 M := ![![![50, 159, 174, -26, 384]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![50, 159, 174, -26, 384]] ![![-77, -245, -268, 40, -591]]
  ![![-88370, -280638, -307050, 45827, -677072]] where
 M := ![![![-88370, -280638, -307050, 45827, -677072]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-88370, -280638, -307050, 45827, -677072]] ![![25, 19, 6, -4, -84]]
  ![![-6, 12, 19, -11, 122]] where
 M := ![![![-6, 12, 19, -11, 122]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-6, 12, 19, -11, 122]] ![![25, 19, 6, -4, -84]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![14950, 7744, -584, 2564, -79160]]]
 hmul := by decide  
 g := ![![![![7475, 3872, -292, 1282, -39580]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1, I2N2, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N2
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![119, 173, -145, 44, -380]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![119, 173, -145, 44, -380]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![119, 173, -145, 44, -380], ![-176, -85, 101, -29, 272], ![116, -20, -16, 3, -50], ![-12, 78, -49, 16, -126], ![4, 27, -19, 6, -49]]]
  hmulB := by decide  
  f := ![![![-47, -149, -163, 24, -358]], ![![-32, -103, -113, 17, -252]], ![![-68, -216, -236, 37, -526]], ![![-148, -446, -483, 68, -1010]], ![![-42, -131, -143, 20, -307]]]
  g := ![![![293, 173, -145, 44, -380], ![-240, -85, 101, -29, 272], ![72, -20, -16, 3, -50], ![80, 78, -49, 16, -126], ![34, 27, -19, 6, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![55, -54, 22, -8, 52]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![55, -54, 22, -8, 52]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![55, -54, 22, -8, 52], ![32, 75, -58, 18, -152], ![-72, -48, 49, -14, 132], ![56, 4, -14, 1, -20], ![16, -2, -2, 0, -5]]]
  hmulB := by decide  
  f := ![![![2021, 6418, 7022, -1048, 15484]], ![![2071, 6577, 7196, -1074, 15868]], ![![4246, 13484, 14753, -2202, 32532]], ![![6687, 21234, 23232, -3467, 51224]], ![![1111, 3528, 3860, -576, 8511]]]
  g := ![![![7, -54, 22, -8, 52], ![69, 75, -58, 18, -152], ![-80, -48, 49, -14, 132], ![33, 4, -14, 1, -20], ![9, -2, -2, 0, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![119, 173, -145, 44, -380]] ![![119, 173, -145, 44, -380]]
  ![![-35155, 1954, 7602, -1792, 22162]] where
 M := ![![![-35155, 1954, 7602, -1792, 22162]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-35155, 1954, 7602, -1792, 22162]] ![![55, -54, 22, -8, 52]]
  ![![-2164101, 1628532, -533480, 208192, -1196574]] where
 M := ![![![-2164101, 1628532, -533480, 208192, -1196574]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![-2164101, 1628532, -533480, 208192, -1196574]] ![![55, -54, 22, -8, 52]]
  ![![-35988403, 267834310, -168727138, 54303296, -428670446]] where
 M := ![![![-35988403, 267834310, -168727138, 54303296, -428670446]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![-35988403, 267834310, -168727138, 54303296, -428670446]] ![![55, -54, 22, -8, 52]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![14921947131, 31204403712, -24496669860, 7525408032, -63796907982]]]
 hmul := by decide  
 g := ![![![![4973982377, 10401467904, -8165556620, 2508469344, -21265635994]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N1, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-51285545, -162868312, -178196520, 26595702, -392938820]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-51285545, -162868312, -178196520, 26595702, -392938820]] 
 ![![5, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![-51285545, -162868312, -178196520, 26595702, -392938820], ![-106382808, -337841557, -369637218, 55168088, -815082204], ![-220672352, -700792660, -766747145, 114436458, -1690744120], ![-457745832, -1453670640, -1590481574, 237378227, -3507150156], ![-33291248, -105723540, -115673618, 17264204, -255070385]]]
  hmulB := by decide  
  f := ![![![-77, -8, 52, 2, -228]], ![![-17, -61, -34, 54, -296]], ![![-276, -44, 107, -114, 1424]], ![![447, 928, 770, -847, 2888]], ![![85, 100, 70, -26, -557]]]
  g := ![![![395317921, -162868312, -178196520, 26595702, -392938820], ![820017229, -337841557, -369637218, 55168088, -815082204], ![1700980958, -700792660, -766747145, 114436458, -1690744120], ![3528384669, -1453670640, -1590481574, 237378227, -3507150156], ![256614743, -105723540, -115673618, 17264204, -255070385]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-51285545, -162868312, -178196520, 26595702, -392938820]] ![![-51285545, -162868312, -178196520, 26595702, -392938820]]
  ![![60186992643175457, 191136779415968544, 209125449335730628, -31211822378700132, 461139798317155136]] where
 M := ![![![60186992643175457, 191136779415968544, 209125449335730628, -31211822378700132, 461139798317155136]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![60186992643175457, 191136779415968544, 209125449335730628, -31211822378700132, 461139798317155136]] ![![-51285545, -162868312, -178196520, 26595702, -392938820]]
  ![![-70633432579408176198657577, -224311703067853008863569032, -245422601754943587105571572, 36629146180081757007871090, -541178175278208637582865844]] where
 M := ![![![-70633432579408176198657577, -224311703067853008863569032, -245422601754943587105571572, 36629146180081757007871090, -541178175278208637582865844]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-70633432579408176198657577, -224311703067853008863569032, -245422601754943587105571572, 36629146180081757007871090, -541178175278208637582865844]] ![![-51285545, -162868312, -178196520, 26595702, -392938820]]
  ![![82893023539622017761786420450940097, 263244678951606436397613269277094528, 288019720428519426470158949228434888, -42986735397975664532988627281247592, 635108525584303569012532804108342208]] where
 M := ![![![82893023539622017761786420450940097, 263244678951606436397613269277094528, 288019720428519426470158949228434888, -42986735397975664532988627281247592, 635108525584303569012532804108342208]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![82893023539622017761786420450940097, 263244678951606436397613269277094528, 288019720428519426470158949228434888, -42986735397975664532988627281247592, 635108525584303569012532804108342208]] ![![-51285545, -162868312, -178196520, 26595702, -392938820]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-97280467628632736152501008018584028938248105, -308935111492476020796928804516208439685605880, -338010267850367238782336671772706048032799040, 50447788520399782728390364833742351454775310, -745342029106231770388907520732781868442189540]]]
 hmul := by decide  
 g := ![![![![-19456093525726547230500201603716805787649621, -61787022298495204159385760903241687937121176, -67602053570073447756467334354541209606559808, 10089557704079956545678072966748470290955062, -149068405821246354077781504146556373688437908]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1 ⊙ MulI5N2 ⊙ MulI5N3)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5485, -5436, -9376, 11986, -93734]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![5485, -5436, -9376, 11986, -93734]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![6, 1, 6, 3, 1]] where
  M :=![![![5485, -5436, -9376, 11986, -93734], ![-47944, -40305, -15268, 12442, 132784], ![-49768, 134608, 179573, -222704, 1518340], ![890816, 577756, 94020, -2543, -3806792], ![102020, -4524, -67520, 94102, -989025]]]
  hmulB := by decide  
  f := ![![![1878563531, 5965783756, 6527248248, -974187090, 14393149902]], ![![3896748360, 12374965073, 13539624028, -2020779114, 29856048192]], ![![8083116456, 25669680096, 28085559467, -4191749480, 61931100540]], ![![16766997920, 53247219076, 58258534276, -8695044193, 128465133400]], ![![16455323370, 52257429303, 57175591310, -8533415737, 126077150003]]]
  g := ![![![81127, 12614, 79004, 41884, -93734], ![-120664, -24727, -115996, -55130, 132784], ![-1308544, -197676, -1275781, -682532, 1518340], ![3390224, 626364, 3276396, 1631119, -3806792], ![862310, 140643, 838090, 437311, -989025]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [2, 3, 4, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 1, 1, 5], [5, 0, 5, 1], [1, 5, 1, 1], [0, 1]]
 g := ![![[1, 5, 4, 1], []], ![[1, 2, 2, 3], [3, 2, 6, 0, 1, 6]], ![[1, 4, 4, 4], [5, 6, 5, 0, 5, 1]], ![[1, 3, 4, 3, 2, 1], [2, 1, 3, 0, 0, 1]]]
 h' := ![![[5, 1, 1, 5], [0, 0, 0, 1], [0, 1]], ![[5, 0, 5, 1], [0, 6, 4], [5, 1, 1, 5]], ![[1, 5, 1, 1], [3, 1, 5], [5, 0, 5, 1]], ![[0, 1], [4, 0, 5, 6], [1, 5, 1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [1, 3, 6], []]
 b := ![[], [], [4, 6, 2, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [2, 3, 4, 3, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2067166396, 6401717860, 5823365066, -6762393417, 30757685041]
  a := ![10, -11, -18, 14, -145]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-26068420550, -3479423883, -25531820740, -14147921220, 30757685041]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1741, 3276, 2592, -2926, 9900]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![1741, 3276, 2592, -2926, 9900]] 
 ![![7, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![1741, 3276, 2592, -2926, 9900], ![11704, -63, -7306, 10248, -110308], ![-40992, -57612, -38635, 41514, -67464], ![-166056, 57600, 165522, -220255, 2003028], ![2272, 29624, 31414, -37600, 210597]]]
  hmulB := by decide  
  f := ![![![-3697811303405, -11743197531252, -12848398240596, 1917614164178, -28331835231852]], ![![-2152297037646, -6835083563007, -7478361442150, 1116140047792, -16490437190356]], ![![-3857777419281, -12251204442072, -13404215775115, 2000569530048, -29557461221340]], ![![-5243198310659, -16650907362660, -18217992867222, 2719022286739, -40172258246040]], ![![-1927687580801, -6121787777284, -6697934450786, 999661882598, -14769527819727]]]
  g := ![![![-5623, 3276, 2592, -2926, 9900], ![50632, -63, -7306, 10248, -110308], ![50145, -57612, -38635, 41514, -67464], ![-938093, 57600, 165522, -220255, 2003028], ![-106487, 29624, 31414, -37600, 210597]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![5485, -5436, -9376, 11986, -93734]] ![![1741, 3276, 2592, -2926, 9900]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![-1873043431, -1527900976, -544438888, 423429468, 5554672662]]]
 hmul := by decide  
 g := ![![![![-267577633, -218271568, -77776984, 60489924, 793524666]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, 51, -31, 10, -78]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-11, 51, -31, 10, -78]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![10, 6, 2, 1, 0], ![1, 9, 7, 0, 1]] where
  M :=![![![-11, 51, -31, 10, -78], ![-40, -49, 43, -13, 112], ![52, 20, -28, 9, -82], ![-36, 6, 1, 0, 30], ![-8, 5, -1, 0, 3]]]
  hmulB := by decide  
  f := ![![![19, 61, 67, -10, 148]], ![![40, 127, 139, -21, 308]], ![![84, 264, 288, -43, 630]], ![![70, 222, 243, -36, 534]], ![![89, 281, 307, -46, 675]]]
  g := ![![![-3, 63, 45, 10, -78], ![-2, -89, -65, -13, 112], ![4, 64, 48, 9, -82], ![-6, -24, -19, 0, 30], ![-1, -2, -2, 0, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [2, 9, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 7, 5], [3, 3, 6], [0, 1]]
 g := ![![[7, 6, 4], [2, 0, 1], []], ![[2, 9, 3, 1], [2, 0, 7, 1], [4, 3]], ![[6, 5, 5, 6], [7, 2, 9, 8], [3, 3]]]
 h' := ![![[8, 7, 5], [7, 4, 9], [0, 0, 1], [0, 1]], ![[3, 3, 6], [4, 9, 3], [1, 4, 3], [8, 7, 5]], ![[0, 1], [2, 9, 10], [3, 7, 7], [3, 3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 5], []]
 b := ![[], [7, 10, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [2, 9, 0, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5673976, -1288872, 2082246, -3195352, 42365592]
  a := ![-9, -52, 17, -13, 132]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1462368, -33037008, -26189654, -3195352, 42365592]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 61, 67, -10, 148]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![19, 61, 67, -10, 148]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![2, 9, 1, 0, 0], ![4, 9, 0, 1, 0], ![7, 2, 0, 0, 1]] where
  M :=![![![19, 61, 67, -10, 148], ![40, 127, 139, -21, 308], ![84, 264, 288, -43, 630], ![172, 542, 593, -84, 1286], ![12, 39, 43, -6, 95]]]
  hmulB := by decide  
  f := ![![![-11, 51, -31, 10, -78]], ![![-40, -49, 43, -13, 112]], ![![-30, -29, 27, -8, 70]], ![![-40, -21, 24, -7, 66]], ![![-15, 24, -12, 4, -29]]]
  g := ![![![-101, -68, 67, -10, 148], ![-210, -141, 139, -21, 308], ![-430, -291, 288, -43, 630], ![-880, -601, 593, -84, 1286], ![-65, -44, 43, -6, 95]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [2, 5, 1] where
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

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [2, 5, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-516, 517, 918, -1111, 8860]
  a := ![3, -5, -5, 4, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5448, -1406, 918, -1111, 8860]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-11, 51, -31, 10, -78]] ![![19, 61, 67, -10, 148]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 5 2 3 [3, 10, 0, 7, 11, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 8, 7, 7, 6], [6, 3, 10, 5, 2], [1, 9, 11, 2, 1], [5, 5, 11, 12, 4], [0, 1]]
 g := ![![[12, 4, 7, 11, 9], [2, 1], []], ![[12, 7, 1, 2, 12, 1, 3, 5], [8, 1, 4, 12], [2, 4, 1, 2, 10, 6, 5, 8]], ![[9, 7, 5, 8, 9, 3, 9, 11], [4, 2, 6, 9], [8, 4, 0, 11, 12, 2, 11, 8]], ![[3, 3, 8, 8, 0, 4], [7, 1, 11, 4], [8, 8, 5, 6, 11, 2, 8, 1]], ![[2, 0, 5, 9, 12, 5, 3, 4], [4, 4, 4, 3], [8, 12, 0, 1, 10, 5, 2, 12]]]
 h' := ![![[3, 8, 7, 7, 6], [7, 3, 3, 12, 10], [0, 0, 0, 1], [0, 1]], ![[6, 3, 10, 5, 2], [1, 1, 3, 6, 9], [8, 2, 7, 2, 8], [3, 8, 7, 7, 6]], ![[1, 9, 11, 2, 1], [10, 5, 8, 3, 8], [10, 11, 6, 11, 3], [6, 3, 10, 5, 2]], ![[5, 5, 11, 12, 4], [1, 11, 4, 11], [3, 1, 12, 9, 11], [1, 9, 11, 2, 1]], ![[0, 1], [10, 6, 8, 7, 12], [10, 12, 1, 3, 4], [5, 5, 11, 12, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 3, 7, 4], [], [], []]
 b := ![[], [10, 3, 9, 6, 8], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 5
  hpos := by decide
  P := [3, 10, 0, 7, 11, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![50468299538280, 27213782121734, -784334983003, 7226953213922, -258851524087312]
  a := ![-15, 35, 27, -23, 218]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3882176887560, 2093367855518, -60333460231, 555919477994, -19911655699024]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 371293 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def PBC13 : ContainsPrimesAboveP 13 ![I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![13, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 13 (by decide) 𝕀

instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1361, -1565, 1381, -414, 3636]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-1361, -1565, 1381, -414, 3636]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![9, 9, 15, 3, 1]] where
  M :=![![![-1361, -1565, 1381, -414, 3636], ![1656, 619, -827, 229, -2196], ![-916, 376, 26, -5, 106], ![20, -830, 447, -50, 346], ![-92, -279, 181, -42, 411]]]
  hmulB := by decide  
  f := ![![![185379, 588711, 644117, -96134, 1420334]], ![![384536, 1221177, 1336107, -199413, 2946232]], ![![797652, 2533116, 2771518, -413647, 6111438]], ![![1654588, 5254502, 5749025, -858038, 12677102]], ![![1304595, 4143023, 4532940, -676538, 9995527]]]
  g := ![![![-2005, -2017, -3127, -666, 3636], ![1260, 1199, 1889, 401, -2196], ![-110, -34, -92, -19, 106], ![-182, -232, -279, -64, 346], ![-223, -234, -352, -75, 411]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 4 2 4 [6, 15, 9, 5, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 7, 10, 12], [2, 10, 8, 2], [0, 16, 16, 3], [0, 1]]
 g := ![![[4, 0, 9, 2], [11, 16, 8], [1], []], ![[9, 11, 3, 6], [11, 3, 9], [9, 14, 4], [12, 13, 8]], ![[11, 2, 2, 15, 16, 13], [11, 16, 8], [12, 1, 2], [8, 12, 4]], ![[0, 0, 2, 9, 13, 14], [11, 3, 9], [5, 13, 13], [16, 0, 9]]]
 h' := ![![[10, 7, 10, 12], [4, 4, 14, 11], [11, 2, 8, 12], [0, 0, 1], [0, 1]], ![[2, 10, 8, 2], [3, 7, 3], [16, 7, 9, 14], [11, 1, 0, 15], [10, 7, 10, 12]], ![[0, 16, 16, 3], [4, 1, 2, 10], [11, 15, 9, 5], [7, 1, 9, 11], [2, 10, 8, 2]], ![[0, 1], [4, 5, 15, 13], [6, 10, 8, 3], [6, 15, 7, 8], [0, 16, 16, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [7, 3, 10], []]
 b := ![[], [], [5, 1, 2, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 4
  hpos := by decide
  P := [6, 15, 9, 5, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![85213564340, 95510457404, 53562867250, -53976481050, -49311423380]
  a := ![19, -20, -33, 30, -276]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![31118610280, 31724309872, 46660836350, 5526928770, -49311423380]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 83521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-185379, -588711, -644117, 96134, -1420334]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-185379, -588711, -644117, 96134, -1420334]] 
 ![![17, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![-185379, -588711, -644117, 96134, -1420334], ![-384536, -1221177, -1336107, 199413, -2946232], ![-797652, -2533116, -2771518, 413647, -6111438], ![-1654588, -5254502, -5749025, 858038, -12677102], ![-120336, -382153, -418119, 62404, -921989]]]
  hmulB := by decide  
  f := ![![![1361, 1565, -1381, 414, -3636]], ![![463, 608, -520, 157, -1368]], ![![214, 162, -164, 49, -434]], ![![239, 325, -270, 76, -662]], ![![806, 937, -823, 246, -2163]]]
  g := ![![![1125810, -588711, -644117, 96134, -1420334], ![2335294, -1221177, -1336107, 199413, -2946232], ![4844155, -2533116, -2771518, 413647, -6111438], ![10048346, -5254502, -5749025, 858038, -12677102], ![730803, -382153, -418119, 62404, -921989]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-1361, -1565, 1381, -414, 3636]] ![![-185379, -588711, -644117, 96134, -1420334]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![-17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![839, 295, -228, 415, -6430]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![839, 295, -228, 415, -6430]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![2, 13, 0, 17, 1]] where
  M :=![![![839, 295, -228, 415, -6430], ![-1660, -3931, -3230, 3712, -14510], ![-14848, -1322, 7543, -10992, 128236], ![43968, 69420, 49970, -54741, 131880], ![10288, 6889, 1330, -313, -42375]]]
  hmulB := by decide  
  f := ![![![127258505, 404136837, 442171820, -65993825, 975027308]], ![![263975300, 838310513, 917207370, -136892538, 2022521998]], ![![547570152, 1738927146, 1902584745, -283959400, 4195364784]], ![![1135837600, 3607097336, 3946576130, -589023639, 8702543504]], ![![1214633846, 3857331814, 4220361206, -629885864, 9306263401]]]
  g := ![![![721, 4415, -12, 5775, -6430], ![1440, 9721, -170, 13178, -14510], ![-14280, -87810, 397, -115316, 128236], ![-11568, -86580, 2630, -120879, 131880], ![5002, 29356, 70, 37898, -42375]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 4 2 4 [4, 2, 14, 14, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 10, 3, 3], [12, 18], [5, 9, 16, 16], [0, 1]]
 g := ![![[3, 1, 10, 7], [14, 17, 4, 6], [1], []], ![[13, 11, 13, 10, 3, 3], [11, 0, 17, 12, 5, 3], [3, 13, 4], [11, 6, 9]], ![[4, 3, 15, 12], [9, 12, 11, 13], [1], []], ![[0, 14, 9, 10, 12, 16], [17, 4, 8, 7, 14, 16], [13, 5, 4], [11, 6, 9]]]
 h' := ![![[7, 10, 3, 3], [1, 15, 17, 11], [15, 17, 5, 5], [0, 0, 1], [0, 1]], ![[12, 18], [18, 8, 12, 18], [13, 8, 1, 1], [5, 18, 16, 17], [7, 10, 3, 3]], ![[5, 9, 16, 16], [15, 12, 14, 8], [3, 2, 14, 14], [11, 14, 1], [12, 18]], ![[0, 1], [0, 3, 14, 1], [5, 11, 18, 18], [0, 6, 1, 2], [5, 9, 16, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [15], []]
 b := ![[], [], [3, 17, 17, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 4
  hpos := by decide
  P := [4, 2, 14, 14, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2339292868, -40302187672, -43199846660, 51796337024, -293443282636]
  a := ![-12, 12, 22, -28, 174]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![30765645916, 198655815084, -2273676140, 265280639044, -293443282636]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 130321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-127258505, -404136837, -442171820, 65993825, -975027308]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-127258505, -404136837, -442171820, 65993825, -975027308]] 
 ![![19, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![-127258505, -404136837, -442171820, 65993825, -975027308], ![-263975300, -838310513, -917207370, 136892538, -2022521998], ![-547570152, -1738927146, -1902584745, 283959400, -4195364784], ![-1135837600, -3607097336, -3946576130, 589023639, -8702543504], ![-82607964, -262339411, -287029254, 42838909, -632924461]]]
  hmulB := by decide  
  f := ![![![-839, -295, 228, -415, 6430]], ![![-575, -26, 350, -523, 5840]], ![![649, 23, -361, 513, -5734]], ![![-2844, -3840, -2486, 2619, -2880]], ![![-1248, -611, 122, -333, 7645]]]
  g := ![![![1161569502, -404136837, -442171820, 65993825, -975027308], ![2409470843, -838310513, -917207370, 136892538, -2022521998], ![4998021843, -1738927146, -1902584745, 283959400, -4195364784], ![10367513854, -3607097336, -3946576130, 589023639, -8702543504], ![754015549, -262339411, -287029254, 42838909, -632924461]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![839, 295, -228, 415, -6430]] ![![-127258505, -404136837, -442171820, 65993825, -975027308]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![-19, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1299, -223, 465, -126, 1292]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-1299, -223, 465, -126, 1292]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![3, 19, 7, 3, 1]] where
  M :=![![![-1299, -223, 465, -126, 1292], ![504, -511, 187, -71, 444], ![284, 664, -564, 169, -1454], ![-676, -494, 393, -124, 1078], ![-220, -113, 123, -36, 333]]]
  hmulB := by decide  
  f := ![![![7, 3, -1, 2, -42]], ![![-8, -27, -25, 29, -136]], ![![-116, -28, 40, -63, 866]], ![![252, 498, 397, -448, 1542]], ![![-5, 37, 44, -54, 337]]]
  g := ![![![-225, -1077, -373, -174, 1292], ![-36, -389, -127, -61, 444], ![202, 1230, 418, 197, -1454], ![-170, -912, -311, -146, 1078], ![-53, -280, -96, -45, 333]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 4 2 4 [4, 10, 12, 9, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 16, 6, 7], [18, 7, 16, 18], [11, 22, 1, 21], [0, 1]]
 g := ![![[21, 9, 19, 6], [18, 13], [14, 1], []], ![[16, 4, 4, 19, 4, 15], [2, 9, 12, 19, 19, 22], [15, 6, 1, 20, 12, 22], [10, 11, 3]], ![[5, 1, 1, 4, 2, 8], [21, 19, 14, 17, 3, 13], [21, 11, 17, 15, 7, 2], [16, 6, 2]], ![[15, 2, 14, 19, 7, 14], [3, 1, 11, 3, 13, 21], [22, 7, 0, 17, 20, 15], [18, 6, 4]]]
 h' := ![![[8, 16, 6, 7], [20, 6, 4, 12], [13, 17, 6], [0, 0, 1], [0, 1]], ![[18, 7, 16, 18], [4, 10, 19, 14], [17, 1, 3, 17], [1, 20, 18, 6], [8, 16, 6, 7]], ![[11, 22, 1, 21], [16, 9, 3, 16], [16, 21, 1, 5], [7, 22, 20, 15], [18, 7, 16, 18]], ![[0, 1], [8, 21, 20, 4], [11, 7, 13, 1], [3, 4, 7, 2], [11, 22, 1, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [20, 20, 21], []]
 b := ![[], [], [2, 17, 12, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 4
  hpos := by decide
  P := [4, 10, 12, 9, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-790054808, 1092262833, 1697344606, -2122325783, 15880893666]
  a := ![1, 11, 2, 9, -8]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2105771122, -13071509427, -4759517872, -2163695947, 15880893666]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 279841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -3, 1, -2, 42]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-7, -3, 1, -2, 42]] 
 ![![23, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![-7, -3, 1, -2, 42], ![8, 27, 25, -29, 136], ![116, 28, -40, 63, -866], ![-252, -498, -397, 448, -1542], ![-72, -57, -19, 14, 227]]]
  hmulB := by decide  
  f := ![![![1299, 223, -465, 126, -1292]], ![![204, 61, -89, 25, -244]], ![![383, 39, -117, 31, -330]], ![![1046, 196, -381, 104, -1058]], ![![179, 34, -66, 18, -183]]]
  g := ![![![-4, -3, 1, -2, 42], ![-7, 27, 25, -29, 136], ![76, 28, -40, 63, -866], ![47, -498, -397, 448, -1542], ![-28, -57, -19, 14, 227]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-1299, -223, 465, -126, 1292]] ![![-7, -3, 1, -2, 42]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![-23, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


lemma PB532I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB532I0 : PrimesBelowBoundCertificateInterval O 1 23 532 where
  m := 9
  g := ![5, 5, 5, 2, 2, 1, 2, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB532I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2, 2, 2]
    · exact ![3, 3, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![2401, 7]
    · exact ![1331, 121]
    · exact ![371293]
    · exact ![83521, 17]
    · exact ![130321, 19]
    · exact ![279841, 23]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N1
      exact NI2N2
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N1
      exact NI3N1
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
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
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N1, I11N1, I17N1, I19N1, I23N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [I11N1], [], [I17N1], [I19N1], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
