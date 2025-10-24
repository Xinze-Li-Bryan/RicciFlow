#!/bin/bash
# 检查 GitHub Actions workflow 状态

echo "=== GitHub Actions Workflow Status ==="
echo ""

# 获取最新的 workflow 运行
gh run list --limit 1 --json status,conclusion,name,createdAt,databaseId,displayTitle | \
python3 -c "
import json, sys, datetime
data = json.load(sys.stdin)
if data:
    run = data[0]
    status = run['status']
    conclusion = run.get('conclusion', 'N/A')
    name = run['name']
    created = run['createdAt']
    run_id = run['databaseId']
    title = run['displayTitle']
    
    # 计算运行时间
    created_time = datetime.datetime.fromisoformat(created.replace('Z', '+00:00'))
    now = datetime.datetime.now(datetime.timezone.utc)
    elapsed = now - created_time
    minutes = int(elapsed.total_seconds() / 60)
    seconds = int(elapsed.total_seconds() % 60)
    
    print(f'Workflow: {name}')
    print(f'Commit: {title}')
    print(f'Status: {status.upper()}')
    if conclusion != 'N/A':
        print(f'Result: {conclusion.upper()}')
    print(f'Running time: {minutes}m {seconds}s')
    print(f'Run ID: {run_id}')
    print()
    
    if status == 'in_progress':
        print('✨ Building with Mathlib cache... Expected steps:')
        print('   - Install dependencies: ~2 min')
        print('   - Download Mathlib cache: ~2 min ⭐')
        print('   - Build RicciFlow: ~1 min')
        print('   - Generate docs: ~3-5 min')
        print('   - Deploy: ~2 min')
        print('   Total: ~8-12 min (much faster!)')
        print()
        print(f'⏱️  Current: {minutes}m {seconds}s (expected: 8-12 min)')
    elif conclusion == 'success':
        print('✅ Deployment successful!')
        print('🌐 Visit: https://xinze-li-bryan.github.io/RicciFlow/')
        print()
        print('Your Blueprint and API docs are now live!')
    else:
        print('❌ Workflow failed. Check logs with:')
        print(f'   gh run view {run_id} --log-failed')
else:
    print('No workflow runs found.')
"
