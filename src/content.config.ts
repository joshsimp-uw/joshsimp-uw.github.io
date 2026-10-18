import { defineCollection } from 'astro:content';
import { glob } from 'astro/loaders';
import { z } from 'astro/zod';

const projects = defineCollection({
  loader: glob({ pattern: '**/*.md', base: './src/content/projects' }),
  schema: z.object({
    title: z.string(),
    summary: z.string(),
    school: z.enum(['UWT', 'OC', 'Udemy']).optional(),
    course: z.string().optional(),
    term: z.string().optional(),
    tags: z.array(z.string()).default([]),
    repo: z.url().optional(),
    demo: z.string().optional(),
    status: z.enum(['complete', 'in-progress', 'archived']).default('complete'),
    featured: z.boolean().default(false),
  }),
});

export const collections = { projects };
