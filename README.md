# mui-dialog

A reusable dialog component for React applications built with Material-UI (MUI).

## Installation

```bash
# Using npm
npm install mui-dialog

# Using yarn
yarn add mui-dialog
```

## Features

- Built with Material-UI (MUI) components
- TypeScript support
- Multiple dialog types:
  - Information
  - Confirmation
  - Input
- Customizable sizes and layouts
- Support for primary, secondary, and tertiary actions
- Responsive design
- Theme customization

## Usage

```tsx
import { MuiDialog } from "mui-dialog";
import { MODAL_TYPES, INFORMATION_SUBTYPES } from "mui-dialog";

// Basic Information Dialog
const MyComponent = () => {
  const [open, setOpen] = useState(false);

  return (
    <MuiDialog
      type={MODAL_TYPES.INFORMATION}
      subtype={INFORMATION_SUBTYPES.ACKNOWLEDGEMENT}
      open={open}
      onClose={() => setOpen(false)}
      title="Dialog Title"
      description="This is a dialog description"
      actions={{
        primaryCtaTitle: "Confirm",
        onPrimaryCtaClick: () => {
          // Handle primary action
          setOpen(false);
        },
      }}
    >
      {/* Optional content */}
    </MuiDialog>
  );
};
```

## Props

## Modal Types

| Type           | Description                          | Subtypes                                 | Allowed Sizes     |
| -------------- | ------------------------------------ | ---------------------------------------- | ----------------- |
| `information`  | For displaying information to users  | `acknowledgement`, `progress`, `passive` | Varies by subtype |
| `confirmation` | For user confirmations and decisions | `default`, `destructive`, `nested`       | `small` only      |
| `input`        | For collecting user input            | `default`, `destructive`                 | All sizes         |

### Subtype Details

#### Information Modal Subtypes

| Subtype           | Description                            | Allowed Sizes                   | Dismissible |
| ----------------- | -------------------------------------- | ------------------------------- | ----------- |
| `acknowledgement` | For simple acknowledgements            | `small`                         | `full`      |
| `progress`        | For showing progress or status updates | `small`, `medium`, `large`      | `partial`   |
| `passive`         | For passive information display        | `medium`, `large`, `extraLarge` | `full`      |

#### Confirmation Modal Subtypes

| Subtype       | Description              | Allowed Sizes | Dismissible |
| ------------- | ------------------------ | ------------- | ----------- |
| `default`     | Standard confirmation    | `small`       | `partial`   |
| `destructive` | For destructive actions  | `small`       | `partial`   |
| `nested`      | For nested confirmations | `small`       | `partial`   |

#### Input Modal Subtypes

| Subtype       | Description                   | Allowed Sizes | Dismissible |
| ------------- | ----------------------------- | ------------- | ----------- |
| `default`     | Standard input                | All sizes     | `partial`   |
| `destructive` | For destructive input actions | All sizes     | `partial`   |

## Props Reference

### Base Props

| Prop               | Type                                             | Required | Default   | Description                    |
| ------------------ | ------------------------------------------------ | -------- | --------- | ------------------------------ |
| `type`             | `"information" \| "confirmation" \| "input"`     | Yes      | -         | Type of the modal              |
| `subtype`          | `string`                                         | Yes      | -         | Subtype of the modal           |
| `open`             | `boolean`                                        | Yes      | -         | Controls modal visibility      |
| `onClose`          | `() => void`                                     | Yes      | -         | Callback when modal is closed  |
| `title`            | `string \| React.ReactNode`                      | No       | -         | Modal title                    |
| `subTitle`         | `string \| React.ReactNode`                      | No       | -         | Modal subtitle                 |
| `description`      | `string \| React.ReactNode`                      | No       | -         | Modal description              |
| `children`         | `React.ReactNode`                                | No       | -         | Additional content             |
| `size`             | `"small" \| "medium" \| "large" \| "extraLarge"` | No       | `"small"` | Modal size                     |
| `wrapperClassName` | `string`                                         | No       | -         | Custom class for modal wrapper |
| `showCloseIcon`    | `boolean`                                        | No       | `true`    | Show/hide close icon           |
| `showDivider`      | `boolean`                                        | No       | `true`    | Show/hide divider              |
| `showActions`      | `boolean`                                        | No       | `true`    | Show/hide action buttons       |

### Action Props

| Prop                     | Type              | Required | Default                                         | Description                             |
| ------------------------ | ----------------- | -------- | ----------------------------------------------- | --------------------------------------- |
| `primaryCtaTitle`        | `string`          | No       | -                                               | Primary button text                     |
| `secondaryCtaTitle`      | `string`          | No       | -                                               | Secondary button text                   |
| `tertiaryCtaTitle`       | `string`          | No       | -                                               | Tertiary button text                    |
| `isPrimaryCtaLoading`    | `boolean`         | No       | `false`                                         | Show loading state for primary button   |
| `isSecondaryCtaLoading`  | `boolean`         | No       | `false`                                         | Show loading state for secondary button |
| `isTertiaryCtaLoading`   | `boolean`         | No       | `false`                                         | Show loading state for tertiary button  |
| `isPrimaryCtaDisabled`   | `boolean`         | No       | `isSecondaryCtaLoading or isTertiaryCtaLoading` | Disable primary button                  |
| `isSecondaryCtaDisabled` | `boolean`         | No       | `isPrimaryCtaLoading or isTertiaryCtaLoading`   | Disable secondary button                |
| `isTertiaryCtaDisabled`  | `boolean`         | No       | `isPrimaryCtaLoading or isSecondaryCtaLoading`  | Disable tertiary button                 |
| `onPrimaryCtaClick`      | `() => void`      | No       | -                                               | Primary button click handler            |
| `onSecondaryCtaClick`    | `() => void`      | No       | -                                               | Secondary button click handler          |
| `onTertiaryCtaClick`     | `() => void`      | No       | -                                               | Tertiary button click handler           |
| `tertiaryCtaStartIcon`   | `React.ReactNode` | No       | -                                               | Icon for tertiary button                |

## Size Breakpoints

| Size         | Breakpoint | Max Width |
| ------------ | ---------- | --------- |
| `small`      | `xs`       | 600px     |
| `medium`     | `sm`       | 900px     |
| `large`      | `md`       | 1200px    |
| `extraLarge` | `lg`       | 1536px    |

## Usage Example

```tsx
import { MuiDialog } from "mui-dialog";

// Input Modal
<MuiDialog
  type="input"
  subtype="default"
  open={true}
  onClose={() => {}}
  title="Input Required"
  description="Please provide your input"
  size="medium"
  actions={{
    primaryCtaTitle: "Submit",
    secondaryCtaTitle: "Cancel",
    onPrimaryCtaClick: () => {},
    onSecondaryCtaClick: () => {},
  }}
>
  <input type="text" />
</MuiDialog>;
```

## Modal Configuration

Each modal type and subtype has specific configurations for:

- Dismissibility: 'full' or 'partial'
- Allowed sizes: Array of allowed size options

These configurations are automatically enforced by the component to ensure consistent behavior across different use cases.

## Development

### Local Setup

```bash
# Install dependencies
yarn install

# Build package
yarn build
```

### Local Development with yarn link

To test the package in another project locally:

1. In the `mui-dialog` directory:

```bash
# Build the package
yarn build

# Create a global symlink
yarn link
```

2. In your project directory:

```bash
# Link to the package
yarn link "mui-dialog"
```

3. To unlink when done:

```bash
# In your project directory
yarn unlink "mui-dialog"

# In the fe-vi-dialog directory
yarn unlink
```

Note: After making changes to the package, you'll need to:

1. Rebuild the package (`yarn build`)

## License

© [Virtual Internships]
