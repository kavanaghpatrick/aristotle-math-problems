#!/usr/bin/env python3
"""Check Aristotle project #22 result"""
import asyncio
from aristotlelib import Project, set_api_key

async def main():
    set_api_key("os.environ["ARISTOTLE_API_KEY"]")

    project_id = "3759e029-5562-4712-90db-b86049fa75b9"

    print(f"🔍 Fetching Aristotle project {project_id}...")
    print(f"📊 Dashboard: https://aristotle.harmonic.fun/project/{project_id}")
    print()

    try:
        project = await Project.get_project_by_id(project_id)

        print(f"✅ Project Status: {project.status}")
        print(f"📝 Project Name: {project.name if hasattr(project, 'name') else 'N/A'}")

        # Print all available attributes
        print("\n📋 Project Details:")
        for attr in dir(project):
            if not attr.startswith('_') and not callable(getattr(project, attr)):
                try:
                    value = getattr(project, attr)
                    if value and str(value) != '':
                        print(f"  {attr}: {value}")
                except:
                    pass

        # Try to get output files
        print("\n📂 Output Files:")
        if hasattr(project, 'output_files'):
            for file in project.output_files:
                print(f"  - {file}")

        # Try to get solution
        print("\n💡 Solution/Result:")
        if hasattr(project, 'solution'):
            print(project.solution)
        elif hasattr(project, 'result'):
            print(project.result)
        elif hasattr(project, 'output'):
            print(project.output)
        else:
            print("  (Check dashboard for detailed results)")

    except Exception as e:
        print(f"❌ Error: {e}")
        import traceback
        traceback.print_exc()

if __name__ == "__main__":
    asyncio.run(main())
