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

const firebaseConfig = {
  apiKey: "AIzaSyCfn09iKdrg6YRJt43iLNiE2SlQfqTk6s0",
  authDomain: "eg-cal-9124c.firebaseapp.com",
  projectId: "eg-cal-9124c",
  appId: "1:935583716243:web:ff103cc05dc321cf61ce66",
};

const isConfigured = !String(firebaseConfig.apiKey).startsWith("YOUR_");

const app = initializeApp(firebaseConfig);
const auth = getAuth(app);

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

window.dispatchEvent(new Event("egcal-auth-ready"));
