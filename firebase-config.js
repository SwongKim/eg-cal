// Firebase 프로젝트 설정.
// https://console.firebase.google.com 에서 프로젝트를 만들고 "웹 앱 추가"로 발급받은 값으로
// 아래 firebaseConfig 를 교체하세요. Authentication > Sign-in method 에서
// "이메일/비밀번호" 제공업체를 사용 설정해야 로그인/회원가입이 동작합니다.
import { initializeApp } from "https://www.gstatic.com/firebasejs/10.12.5/firebase-app.js";
import {
  getAuth,
  onAuthStateChanged,
  createUserWithEmailAndPassword,
  signInWithEmailAndPassword,
  sendPasswordResetEmail,
  signOut,
} from "https://www.gstatic.com/firebasejs/10.12.5/firebase-auth.js";
import {
  getFirestore,
  collection,
  addDoc,
  deleteDoc,
  doc,
  getDocs,
  query,
  orderBy,
  limit,
  Timestamp,
} from "https://www.gstatic.com/firebasejs/10.12.5/firebase-firestore.js";

const firebaseConfig = {
  apiKey: "AIzaSyCfn09iKdrg6YRJt43iLNiE2SlQfqTk6s0",
  authDomain: "eg-cal-9124c.firebaseapp.com",
  projectId: "eg-cal-9124c",
  appId: "1:935583716243:web:ff103cc05dc321cf61ce66",
};

const isConfigured = !String(firebaseConfig.apiKey).startsWith("YOUR_");

const app = initializeApp(firebaseConfig);
const auth = getAuth(app);
const db = getFirestore(app);
const HISTORY_LIMIT = 10;

const listeners = new Set();
let lastUser = undefined;
onAuthStateChanged(auth, (user) => {
  lastUser = user;
  listeners.forEach((cb) => cb(user));
});

window.EgCalAuth = {
  isConfigured,
  onAuthChange(cb) {
    listeners.add(cb);
    if (lastUser !== undefined) cb(lastUser);
    return () => listeners.delete(cb);
  },
  async login(email, password) {
    const cred = await signInWithEmailAndPassword(auth, email, password);
    return cred.user;
  },
  async signup(email, password) {
    const cred = await createUserWithEmailAndPassword(auth, email, password);
    return cred.user;
  },
  async resetPassword(email) {
    await sendPasswordResetEmail(auth, email);
  },
  async logout() {
    await signOut(auth);
  },
};

// 계정별 결과 저장 이력 — 사용자당 최신 10개까지만 유지 (users/{uid}/history 하위 컬렉션).
// Firestore 콘솔에서 해당 프로젝트의 Firestore Database 를 생성하고, 보안 규칙에서
// 본인 uid 하위 문서만 읽고 쓸 수 있도록 설정해야 동작합니다.
window.EgCalHistory = {
  isConfigured,
  HISTORY_LIMIT,
  async list(uid) {
    if (!uid) return [];
    const col = collection(db, "users", uid, "history");
    const q = query(col, orderBy("createdAt", "desc"), limit(HISTORY_LIMIT));
    const snap = await getDocs(q);
    return snap.docs.map((d) => ({ id: d.id, ...d.data() }));
  },
  async save(uid, data) {
    if (!uid) throw new Error("not-authenticated");
    const existing = await this.list(uid);
    if (existing.length >= HISTORY_LIMIT) {
      const oldest = existing[existing.length - 1];
      if (oldest) await deleteDoc(doc(db, "users", uid, "history", oldest.id));
    }
    const record = { rows: data.rows, logX: !!data.logX, logY: !!data.logY, memo: String(data.memo || ""), createdAt: Timestamp.now() };
    const ref = await addDoc(collection(db, "users", uid, "history"), record);
    return { id: ref.id, ...record };
  },
};

window.dispatchEvent(new Event("egcal-auth-ready"));
