# joshsimp-uw.github.io

Project gallery of coursework and side projects from the University of Washington Tacoma, built with [Astro](https://astro.build) and deployed to GitHub Pages.

## Develop

```sh
npm install
npm run dev      # http://localhost:4321
npm run build    # static output in dist/
```

## Add a project

Create `src/content/projects/<slug>.md`:

```markdown
---
title: Project Name
summary: One-sentence description.
school: UWT          # UWT | OC | Udemy (optional)
course: TINFO 200    # optional
term: 2026 Spring    # optional
tags: [csharp]
repo: https://github.com/joshsimp-uw/<repo>   # optional
demo: /demos/<slug>/                          # optional, served from public/demos/
status: complete     # complete | in-progress | archived
featured: false
---

What the project is and how it works.

## What I learned

Every project needs this section; the build fails without it.
```

Static demos (plain HTML/CSS/JS) go in `public/demos/<slug>/`.


