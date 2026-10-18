import { getCollection, type CollectionEntry } from 'astro:content';

export type Project = CollectionEntry<'projects'>;

const REFLECTION_HEADING = /^## What I learned\s*$/m;

/**
 * Returns every project, featured first, then alphabetical.
 * Fails the build if a project is missing its "What I learned" section,
 * since every project on this site is required to have one.
 */
export async function getProjects(): Promise<Project[]> {
  const projects = await getCollection('projects');

  const missing = projects.filter((p) => !REFLECTION_HEADING.test(p.body ?? ''));
  if (missing.length > 0) {
    const ids = missing.map((p) => p.id).join(', ');
    throw new Error(`Projects missing a "## What I learned" section: ${ids}`);
  }

  return projects.sort(
    (a, b) =>
      Number(b.data.featured) - Number(a.data.featured) ||
      a.data.title.localeCompare(b.data.title),
  );
}

export function courseLabel(project: Project): string | undefined {
  const { school, course } = project.data;
  if (school && course) return `${school} ${course}`;
  return course ?? school;
}
