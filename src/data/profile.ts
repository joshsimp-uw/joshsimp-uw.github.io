export const EMAIL = 'joshsimp@uw.edu';

export interface Degree {
  title: string;
  school: string;
  /** Year conferred, or expected year while in progress */
  year: number;
  inProgress?: boolean;
  honors?: string;
}

export interface Certification {
  title: string;
  issuer: string;
  /** Year earned; a range where the exact year isn't known */
  year: string;
}

/** Newest first */
export const degrees: Degree[] = [
  {
    title: 'Master of Cybersecurity and Leadership',
    school: 'University of Washington Tacoma',
    year: 2027,
    inProgress: true,
  },
  {
    title: 'Bachelor of Science in Information Technology',
    school: 'University of Washington Tacoma',
    year: 2026,
    honors: 'Magna Cum Laude',
  },
  {
    title: 'AAS-T in Information Technology: Security',
    school: 'Olympic College',
    year: 2023,
  },
  {
    title: 'AAS-T in Information Technology: Networking',
    school: 'Olympic College',
    year: 2022,
  },
];

/** Newest first */
export const certifications: Certification[] = [
  { title: 'Security+', issuer: 'CompTIA', year: '2022' },
  { title: 'Network+', issuer: 'CompTIA', year: '2022' },
  { title: 'A+', issuer: 'CompTIA', year: '2022' },
  { title: 'MCSE: Windows NT 4.0', issuer: 'Microsoft', year: '2000–2001' },
];
